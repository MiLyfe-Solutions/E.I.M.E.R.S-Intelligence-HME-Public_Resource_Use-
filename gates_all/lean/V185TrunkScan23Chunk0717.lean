import V185TrunkScan23Chunk0716

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4239008 : List Nat := [2, 1, 1, 4, 3, 1, 3, 2, 6]
def baseStart_4239008 : Nat := 118140960795 + 4239008 * 2 ^ 59
def prefixEnd_4239008 : Nat := 4983230072969 + 3 ^ 40 * 4239008 * 2
def baseEnd_4239008 : Nat := 241849844694917343933907

theorem tailTrace_4239008 : CollatzResearch.WordTrace tailWord_4239008 prefixEnd_4239008 241849844694917343933907 := by
  unfold tailWord_4239008
  simp only [CollatzResearch.WordTrace]
  refine ⟨77304661713402727886858839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103072882284536970515811785 77304661713402727886858839)
  ·
    refine ⟨115956992570104091830288259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77304661713402727886858839 115956992570104091830288259)
    ·
      refine ⟨173935488855156137745432389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115956992570104091830288259 173935488855156137745432389)
      ·
        refine ⟨32612904160341775827268573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 173935488855156137745432389 32612904160341775827268573)
        ·
          refine ⟨12229839060128165935225715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32612904160341775827268573 12229839060128165935225715)
          ·
            refine ⟨18344758590192248902838573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12229839060128165935225715 18344758590192248902838573)
            ·
              refine ⟨6879284471322093338564465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18344758590192248902838573 6879284471322093338564465)
              ·
                refine ⟨5159463353491570003923349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6879284471322093338564465 5159463353491570003923349)
                ·
                  refine ⟨241849844694917343933907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5159463353491570003923349 241849844694917343933907)
                  ·
                    rfl

theorem cell23_4239008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 2, 6].length) (baseStart_4239008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4239008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4239008 prefixEnd_4239008 := by exact prefixLift 4239008
  have htrace : WordTrace (prefixWord ++ tailWord_4239008) baseStart_4239008 baseEnd_4239008 := by
    simpa [prefixWord, tailWord_4239008, baseEnd_4239008] using wordTrace_append hprefix tailTrace_4239008
  have hstable : (prefixWord ++ tailWord_4239008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4239008).length < 2 ^ (prefixWord ++ tailWord_4239008).sum := by decide
  have hdescent : baseEnd_4239008 < baseStart_4239008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4239008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4239046 : List Nat := [6, 1, 2, 1, 1, 1, 3, 3, 1, 4]
def baseStart_4239046 : Nat := 118140960795 + 4239046 * 2 ^ 59
def prefixEnd_4239046 : Nat := 4983230072969 + 3 ^ 40 * 4239046 * 2
def baseEnd_4239046 : Nat := 725556038173042315576663

theorem tailTrace_4239046 : CollatzResearch.WordTrace tailWord_4239046 prefixEnd_4239046 725556038173042315576663 := by
  unfold tailWord_4239046
  simp only [CollatzResearch.WordTrace]
  refine ⟨4831584668770868383237531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 103073806267111858842400661 4831584668770868383237531)
  ·
    refine ⟨7247377003156302574856297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4831584668770868383237531 7247377003156302574856297)
    ·
      refine ⟨5435532752367226931142223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7247377003156302574856297 5435532752367226931142223)
      ·
        refine ⟨8153299128550840396713335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5435532752367226931142223 8153299128550840396713335)
        ·
          refine ⟨12229948692826260595070003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8153299128550840396713335 12229948692826260595070003)
          ·
            refine ⟨18344923039239390892605005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12229948692826260595070003 18344923039239390892605005)
            ·
              refine ⟨6879346139714771584726877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18344923039239390892605005 6879346139714771584726877)
              ·
                refine ⟨2579754802393039344272579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6879346139714771584726877 2579754802393039344272579)
                ·
                  refine ⟨3869632203589559016408869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2579754802393039344272579 3869632203589559016408869)
                  ·
                    refine ⟨725556038173042315576663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3869632203589559016408869 725556038173042315576663)
                    ·
                      rfl

theorem cell23_4239046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_4239046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4239046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4239046 prefixEnd_4239046 := by exact prefixLift 4239046
  have htrace : WordTrace (prefixWord ++ tailWord_4239046) baseStart_4239046 baseEnd_4239046 := by
    simpa [prefixWord, tailWord_4239046, baseEnd_4239046] using wordTrace_append hprefix tailTrace_4239046
  have hstable : (prefixWord ++ tailWord_4239046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4239046).length < 2 ^ (prefixWord ++ tailWord_4239046).sum := by decide
  have hdescent : baseEnd_4239046 < baseStart_4239046 := by decide
  rcases family_descends (prefixWord ++ tailWord_4239046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4239051 : List Nat := [1, 1, 1, 1, 3, 2, 1, 6, 1, 6]
def baseStart_4239051 : Nat := 118140960795 + 4239051 * 2 ^ 59
def prefixEnd_4239051 : Nat := 4983230072969 + 3 ^ 40 * 4239051 * 2
def baseEnd_4239051 : Nat := 725556893974133142389155

theorem tailTrace_4239051 : CollatzResearch.WordTrace tailWord_4239051 prefixEnd_4239051 725556893974133142389155 := by
  unfold tailWord_4239051
  simp only [CollatzResearch.WordTrace]
  refine ⟨154610891765649674117533007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103073927843766449411688671 154610891765649674117533007)
  ·
    refine ⟨231916337648474511176299511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154610891765649674117533007 231916337648474511176299511)
    ·
      refine ⟨347874506472711766764449267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231916337648474511176299511 347874506472711766764449267)
      ·
        refine ⟨521811759709067650146673901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 347874506472711766764449267 521811759709067650146673901)
        ·
          refine ⟨195679409890900368805002713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 521811759709067650146673901 195679409890900368805002713)
          ·
            refine ⟨146759557418175276603752035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 195679409890900368805002713 146759557418175276603752035)
            ·
              refine ⟨220139336127262914905628053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146759557418175276603752035 220139336127262914905628053)
              ·
                refine ⟨10319031380965449136201315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 220139336127262914905628053 10319031380965449136201315)
                ·
                  refine ⟨15478547071448173704301973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10319031380965449136201315 15478547071448173704301973)
                  ·
                    refine ⟨725556893974133142389155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15478547071448173704301973 725556893974133142389155)
                    ·
                      rfl

theorem cell23_4239051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 6].length) (baseStart_4239051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4239051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4239051 prefixEnd_4239051 := by exact prefixLift 4239051
  have htrace : WordTrace (prefixWord ++ tailWord_4239051) baseStart_4239051 baseEnd_4239051 := by
    simpa [prefixWord, tailWord_4239051, baseEnd_4239051] using wordTrace_append hprefix tailTrace_4239051
  have hstable : (prefixWord ++ tailWord_4239051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4239051).length < 2 ^ (prefixWord ++ tailWord_4239051).sum := by decide
  have hdescent : baseEnd_4239051 < baseStart_4239051 := by decide
  rcases family_descends (prefixWord ++ tailWord_4239051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4239071 : List Nat := [1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 6]
def baseStart_4239071 : Nat := 118140960795 + 4239071 * 2 ^ 59
def prefixEnd_4239071 : Nat := 4983230072969 + 3 ^ 40 * 4239071 * 2
def baseEnd_4239071 : Nat := 2176680951535489348917373

theorem tailTrace_4239071 : CollatzResearch.WordTrace tailWord_4239071 prefixEnd_4239071 2176680951535489348917373 := by
  unfold tailWord_4239071
  simp only [CollatzResearch.WordTrace]
  refine ⟨154611621225577217533261067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103074414150384811688840711 154611621225577217533261067)
  ·
    refine ⟨231917431838365826299891601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154611621225577217533261067 231917431838365826299891601)
    ·
      refine ⟨173938073878774369724918701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231917431838365826299891601 173938073878774369724918701)
      ·
        refine ⟨65226777704540388646844513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 173938073878774369724918701 65226777704540388646844513)
        ·
          refine ⟨48920083278405291485133385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65226777704540388646844513 48920083278405291485133385)
          ·
            refine ⟨36690062458803968613850039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48920083278405291485133385 36690062458803968613850039)
            ·
              refine ⟨55035093688205952920775059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36690062458803968613850039 55035093688205952920775059)
              ·
                refine ⟨82552640532308929381162589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55035093688205952920775059 82552640532308929381162589)
                ·
                  refine ⟨30957240199615848517935971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82552640532308929381162589 30957240199615848517935971)
                  ·
                    refine ⟨46435860299423772776903957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30957240199615848517935971 46435860299423772776903957)
                    ·
                      refine ⟨2176680951535489348917373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46435860299423772776903957 2176680951535489348917373)
                      ·
                        rfl

theorem cell23_4239071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_4239071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4239071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4239071 prefixEnd_4239071 := by exact prefixLift 4239071
  have htrace : WordTrace (prefixWord ++ tailWord_4239071) baseStart_4239071 baseEnd_4239071 := by
    simpa [prefixWord, tailWord_4239071, baseEnd_4239071] using wordTrace_append hprefix tailTrace_4239071
  have hstable : (prefixWord ++ tailWord_4239071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4239071).length < 2 ^ (prefixWord ++ tailWord_4239071).sum := by decide
  have hdescent : baseEnd_4239071 < baseStart_4239071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4239071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4239095 : List Nat := [1, 1, 3, 1, 1, 1, 7, 2, 1, 2, 3]
def baseStart_4239095 : Nat := 118140960795 + 4239095 * 2 ^ 59
def prefixEnd_4239095 : Nat := 4983230072969 + 3 ^ 40 * 4239095 * 2
def baseEnd_4239095 : Nat := 2176693275071197255017263

theorem tailTrace_4239095 : CollatzResearch.WordTrace tailWord_4239095 prefixEnd_4239095 2176693275071197255017263 := by
  unfold tailWord_4239095
  simp only [CollatzResearch.WordTrace]
  refine ⟨154612496577490269632134739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103074997718326846421423159 154612496577490269632134739)
  ·
    refine ⟨231918744866235404448202109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154612496577490269632134739 231918744866235404448202109)
    ·
      refine ⟨86969529324838276668075791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 231918744866235404448202109 86969529324838276668075791)
      ·
        refine ⟨130454293987257415002113687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86969529324838276668075791 130454293987257415002113687)
        ·
          refine ⟨195681440980886122503170531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130454293987257415002113687 195681440980886122503170531)
          ·
            refine ⟨293522161471329183754755797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195681440980886122503170531 293522161471329183754755797)
            ·
              refine ⟨6879425659484277744252089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 293522161471329183754755797 6879425659484277744252089)
              ·
                refine ⟨5159569244613208308189067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6879425659484277744252089 5159569244613208308189067)
                ·
                  refine ⟨7739353866919812462283601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5159569244613208308189067 7739353866919812462283601)
                  ·
                    refine ⟨5804515400189859346712701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7739353866919812462283601 5804515400189859346712701)
                    ·
                      refine ⟨2176693275071197255017263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5804515400189859346712701 2176693275071197255017263)
                      ·
                        rfl

theorem cell23_4239095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 2, 1, 2, 3].length) (baseStart_4239095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4239095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4239095 prefixEnd_4239095 := by exact prefixLift 4239095
  have htrace : WordTrace (prefixWord ++ tailWord_4239095) baseStart_4239095 baseEnd_4239095 := by
    simpa [prefixWord, tailWord_4239095, baseEnd_4239095] using wordTrace_append hprefix tailTrace_4239095
  have hstable : (prefixWord ++ tailWord_4239095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4239095).length < 2 ^ (prefixWord ++ tailWord_4239095).sum := by decide
  have hdescent : baseEnd_4239095 < baseStart_4239095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4239095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4239112 : List Nat := [2, 1, 3, 2, 2, 1, 5, 1, 1, 2, 3]
def baseStart_4239112 : Nat := 118140960795 + 4239112 * 2 ^ 59
def prefixEnd_4239112 : Nat := 4983230072969 + 3 ^ 40 * 4239112 * 2
def baseEnd_4239112 : Nat := 2176702004242323688504685

theorem tailTrace_4239112 : CollatzResearch.WordTrace tailWord_4239112 prefixEnd_4239112 2176702004242323688504685 := by
  unfold tailWord_4239112
  simp only [CollatzResearch.WordTrace]
  refine ⟨77306558309214340767751795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103075411078952454357002393 77306558309214340767751795)
  ·
    refine ⟨115959837463821511151627693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77306558309214340767751795 115959837463821511151627693)
    ·
      refine ⟨43484939048933066681860385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115959837463821511151627693 43484939048933066681860385)
      ·
        refine ⟨32613704286699800011395289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43484939048933066681860385 32613704286699800011395289)
        ·
          refine ⟨24460278215024850008546467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32613704286699800011395289 24460278215024850008546467)
          ·
            refine ⟨36690417322537275012819701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24460278215024850008546467 36690417322537275012819701)
            ·
              refine ⟨3439726623987869532451847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36690417322537275012819701 3439726623987869532451847)
              ·
                refine ⟨5159589935981804298677771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3439726623987869532451847 5159589935981804298677771)
                ·
                  refine ⟨7739384903972706448016657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5159589935981804298677771 7739384903972706448016657)
                  ·
                    refine ⟨5804538677979529836012493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7739384903972706448016657 5804538677979529836012493)
                    ·
                      refine ⟨2176702004242323688504685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5804538677979529836012493 2176702004242323688504685)
                      ·
                        rfl

theorem cell23_4239112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 1, 1, 2, 3].length) (baseStart_4239112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4239112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4239112 prefixEnd_4239112 := by exact prefixLift 4239112
  have htrace : WordTrace (prefixWord ++ tailWord_4239112) baseStart_4239112 baseEnd_4239112 := by
    simpa [prefixWord, tailWord_4239112, baseEnd_4239112] using wordTrace_append hprefix tailTrace_4239112
  have hstable : (prefixWord ++ tailWord_4239112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4239112).length < 2 ^ (prefixWord ++ tailWord_4239112).sum := by decide
  have hdescent : baseEnd_4239112 < baseStart_4239112 := by decide
  rcases family_descends (prefixWord ++ tailWord_4239112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4239135 : List Nat := [1, 1, 2, 4, 2, 1, 1, 1, 5, 3, 2]
def baseStart_4239135 : Nat := 118140960795 + 4239135 * 2 ^ 59
def prefixEnd_4239135 : Nat := 4983230072969 + 3 ^ 40 * 4239135 * 2
def baseEnd_4239135 : Nat := 2176713814297377098517079

theorem tailTrace_4239135 : CollatzResearch.WordTrace tailWord_4239135 prefixEnd_4239135 2176713814297377098517079 := by
  unfold tailWord_4239135
  simp only [CollatzResearch.WordTrace]
  refine ⟨154613955497345356463590859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103075970331563570975727239 154613955497345356463590859)
  ·
    refine ⟨231920933246018034695386289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154613955497345356463590859 231920933246018034695386289)
    ·
      refine ⟨173940699934513526021539717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231920933246018034695386289 173940699934513526021539717)
      ·
        refine ⟨32613881237721286129038697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 173940699934513526021539717 32613881237721286129038697)
        ·
          refine ⟨24460410928290964596779023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32613881237721286129038697 24460410928290964596779023)
          ·
            refine ⟨36690616392436446895168535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24460410928290964596779023 36690616392436446895168535)
            ·
              refine ⟨55035924588654670342752803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36690616392436446895168535 55035924588654670342752803)
              ·
                refine ⟨82553886882982005514129205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55035924588654670342752803 82553886882982005514129205)
                ·
                  refine ⟨7739426895279563016949613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 82553886882982005514129205 7739426895279563016949613)
                  ·
                    refine ⟨2902285085729836131356105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7739426895279563016949613 2902285085729836131356105)
                    ·
                      refine ⟨2176713814297377098517079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2902285085729836131356105 2176713814297377098517079)
                      ·
                        rfl

theorem cell23_4239135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 5, 3, 2].length) (baseStart_4239135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4239135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4239135 prefixEnd_4239135 := by exact prefixLift 4239135
  have htrace : WordTrace (prefixWord ++ tailWord_4239135) baseStart_4239135 baseEnd_4239135 := by
    simpa [prefixWord, tailWord_4239135, baseEnd_4239135] using wordTrace_append hprefix tailTrace_4239135
  have hstable : (prefixWord ++ tailWord_4239135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4239135).length < 2 ^ (prefixWord ++ tailWord_4239135).sum := by decide
  have hdescent : baseEnd_4239135 < baseStart_4239135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4239135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4239178 : List Nat := [3, 1, 2, 1, 1, 1, 3, 1, 4, 2, 4]
def baseStart_4239178 : Nat := 118140960795 + 4239178 * 2 ^ 59
def prefixEnd_4239178 : Nat := 4983230072969 + 3 ^ 40 * 4239178 * 2
def baseEnd_4239178 : Nat := 2176735893965520430279381

theorem tailTrace_4239178 : CollatzResearch.WordTrace tailWord_4239178 prefixEnd_4239178 2176735893965520430279381 := by
  unfold tailWord_4239178
  simp only [CollatzResearch.WordTrace]
  refine ⟨38653880959047393701851547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103077015890793049871604125 38653880959047393701851547)
  ·
    refine ⟨57980821438571090552777321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38653880959047393701851547 57980821438571090552777321)
    ·
      refine ⟨43485616078928317914582991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57980821438571090552777321 43485616078928317914582991)
      ·
        refine ⟨65228424118392476871874487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43485616078928317914582991 65228424118392476871874487)
        ·
          refine ⟨97842636177588715307811731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65228424118392476871874487 97842636177588715307811731)
          ·
            refine ⟨146763954266383072961717597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97842636177588715307811731 146763954266383072961717597)
            ·
              refine ⟨55036482849893652360644099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 146763954266383072961717597 55036482849893652360644099)
              ·
                refine ⟨82554724274840478540966149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55036482849893652360644099 82554724274840478540966149)
                ·
                  refine ⟨15479010801532589726431153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82554724274840478540966149 15479010801532589726431153)
                  ·
                    refine ⟨11609258101149442294823365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15479010801532589726431153 11609258101149442294823365)
                    ·
                      refine ⟨2176735893965520430279381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11609258101149442294823365 2176735893965520430279381)
                      ·
                        rfl

theorem cell23_4239178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_4239178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4239178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4239178 prefixEnd_4239178 := by exact prefixLift 4239178
  have htrace : WordTrace (prefixWord ++ tailWord_4239178) baseStart_4239178 baseEnd_4239178 := by
    simpa [prefixWord, tailWord_4239178, baseEnd_4239178] using wordTrace_append hprefix tailTrace_4239178
  have hstable : (prefixWord ++ tailWord_4239178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4239178).length < 2 ^ (prefixWord ++ tailWord_4239178).sum := by decide
  have hdescent : baseEnd_4239178 < baseStart_4239178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4239178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4239235 : List Nat := [1, 1, 1, 3, 4, 3, 1, 2, 2, 5]
def baseStart_4239235 : Nat := 118140960795 + 4239235 * 2 ^ 59
def prefixEnd_4239235 : Nat := 4983230072969 + 3 ^ 40 * 4239235 * 2
def baseEnd_4239235 : Nat := 725588387454275569088873

theorem tailTrace_4239235 : CollatzResearch.WordTrace tailWord_4239235 prefixEnd_4239235 725588387454275569088873 := by
  unfold tailWord_4239235
  simp only [CollatzResearch.WordTrace]
  refine ⟨154617602796983073542231159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103078401864655382361487439 154617602796983073542231159)
  ·
    refine ⟨231926404195474610313346739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154617602796983073542231159 231926404195474610313346739)
    ·
      refine ⟨347889606293211915470020109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231926404195474610313346739 347889606293211915470020109)
      ·
        refine ⟨130458602359954468301257541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 347889606293211915470020109 130458602359954468301257541)
        ·
          refine ⟨24460987942491462806485789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 130458602359954468301257541 24460987942491462806485789)
          ·
            refine ⟨9172870478434298552432171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24460987942491462806485789 9172870478434298552432171)
            ·
              refine ⟨13759305717651447828648257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9172870478434298552432171 13759305717651447828648257)
              ·
                refine ⟨10319479288238585871486193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13759305717651447828648257 10319479288238585871486193)
                ·
                  refine ⟨7739609466178939403614645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10319479288238585871486193 7739609466178939403614645)
                  ·
                    refine ⟨725588387454275569088873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7739609466178939403614645 725588387454275569088873)
                    ·
                      rfl

theorem cell23_4239235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 2, 5].length) (baseStart_4239235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4239235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4239235 prefixEnd_4239235 := by exact prefixLift 4239235
  have htrace : WordTrace (prefixWord ++ tailWord_4239235) baseStart_4239235 baseEnd_4239235 := by
    simpa [prefixWord, tailWord_4239235, baseEnd_4239235] using wordTrace_append hprefix tailTrace_4239235
  have hstable : (prefixWord ++ tailWord_4239235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4239235).length < 2 ^ (prefixWord ++ tailWord_4239235).sum := by decide
  have hdescent : baseEnd_4239235 < baseStart_4239235 := by decide
  rcases family_descends (prefixWord ++ tailWord_4239235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4239239 : List Nat := [1, 1, 4, 2, 4, 1, 3, 2, 5]
def baseStart_4239239 : Nat := 118140960795 + 4239239 * 2 ^ 59
def prefixEnd_4239239 : Nat := 4983230072969 + 3 ^ 40 * 4239239 * 2
def baseEnd_4239239 : Nat := 241863024031716076846289

theorem tailTrace_4239239 : CollatzResearch.WordTrace tailWord_4239239 prefixEnd_4239239 241863024031716076846289 := by
  unfold tailWord_4239239
  simp only [CollatzResearch.WordTrace]
  refine ⟨154617748688968582225376771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103078499125979054816917847 154617748688968582225376771)
  ·
    refine ⟨231926623033452873338065157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154617748688968582225376771 231926623033452873338065157)
    ·
      refine ⟨43486241818772413750887217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 231926623033452873338065157 43486241818772413750887217)
      ·
        refine ⟨32614681364079310313165413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43486241818772413750887217 32614681364079310313165413)
        ·
          refine ⟨6115252755764870683718515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32614681364079310313165413 6115252755764870683718515)
          ·
            refine ⟨9172879133647306025577773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6115252755764870683718515 9172879133647306025577773)
            ·
              refine ⟨3439829675117739759591665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9172879133647306025577773 3439829675117739759591665)
              ·
                refine ⟨2579872256338304819693749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3439829675117739759591665 2579872256338304819693749)
                ·
                  refine ⟨241863024031716076846289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2579872256338304819693749 241863024031716076846289)
                  ·
                    rfl

theorem cell23_4239239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 2, 5].length) (baseStart_4239239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4239239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4239239 prefixEnd_4239239 := by exact prefixLift 4239239
  have htrace : WordTrace (prefixWord ++ tailWord_4239239) baseStart_4239239 baseEnd_4239239 := by
    simpa [prefixWord, tailWord_4239239, baseEnd_4239239] using wordTrace_append hprefix tailTrace_4239239
  have hstable : (prefixWord ++ tailWord_4239239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4239239).length < 2 ^ (prefixWord ++ tailWord_4239239).sum := by decide
  have hdescent : baseEnd_4239239 < baseStart_4239239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4239239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4239295 : List Nat := [1, 1, 2, 2, 2, 1, 6, 2, 6]
def baseStart_4239295 : Nat := 118140960795 + 4239295 * 2 ^ 59
def prefixEnd_4239295 : Nat := 4983230072969 + 3 ^ 40 * 4239295 * 2
def baseEnd_4239295 : Nat := 241866219022455163612927

theorem tailTrace_4239295 : CollatzResearch.WordTrace tailWord_4239295 prefixEnd_4239295 241866219022455163612927 := by
  unfold tailWord_4239295
  simp only [CollatzResearch.WordTrace]
  refine ⟨154619791176765703789415339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103079860784510469192943559 154619791176765703789415339)
  ·
    refine ⟨231929686765148555684123009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154619791176765703789415339 231929686765148555684123009)
    ·
      refine ⟨173947265073861416763092257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231929686765148555684123009 173947265073861416763092257)
      ·
        refine ⟨130460448805396062572319193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173947265073861416763092257 130460448805396062572319193)
        ·
          refine ⟨97845336604047046929239395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130460448805396062572319193 97845336604047046929239395)
          ·
            refine ⟨146768004906070570393859093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97845336604047046929239395 146768004906070570393859093)
            ·
              refine ⟨6879750229972057987212145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 146768004906070570393859093 6879750229972057987212145)
              ·
                refine ⟨5159812672479043490409109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6879750229972057987212145 5159812672479043490409109)
                ·
                  refine ⟨241866219022455163612927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5159812672479043490409109 241866219022455163612927)
                  ·
                    rfl

theorem cell23_4239295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 2, 6].length) (baseStart_4239295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4239295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4239295 prefixEnd_4239295 := by exact prefixLift 4239295
  have htrace : WordTrace (prefixWord ++ tailWord_4239295) baseStart_4239295 baseEnd_4239295 := by
    simpa [prefixWord, tailWord_4239295, baseEnd_4239295] using wordTrace_append hprefix tailTrace_4239295
  have hstable : (prefixWord ++ tailWord_4239295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4239295).length < 2 ^ (prefixWord ++ tailWord_4239295).sum := by decide
  have hdescent : baseEnd_4239295 < baseStart_4239295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4239295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4239332 : List Nat := [2, 3, 1, 1, 1, 1, 5, 1, 1, 5, 2]
def baseStart_4239332 : Nat := 118140960795 + 4239332 * 2 ^ 59
def prefixEnd_4239332 : Nat := 4983230072969 + 3 ^ 40 * 4239332 * 2
def baseEnd_4239332 : Nat := 2176814969986312827753673

theorem tailTrace_4239332 : CollatzResearch.WordTrace tailWord_4239332 prefixEnd_4239332 2176814969986312827753673 := by
  unfold tailWord_4239332
  simp only [CollatzResearch.WordTrace]
  refine ⟨77310570338815829554256125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103080760451754439405674833 77310570338815829554256125)
  ·
    refine ⟨28991463877055936082846047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77310570338815829554256125 28991463877055936082846047)
    ·
      refine ⟨43487195815583904124269071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28991463877055936082846047 43487195815583904124269071)
      ·
        refine ⟨65230793723375856186403607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43487195815583904124269071 65230793723375856186403607)
        ·
          refine ⟨97846190585063784279605411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65230793723375856186403607 97846190585063784279605411)
          ·
            refine ⟨146769285877595676419408117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97846190585063784279605411 146769285877595676419408117)
            ·
              refine ⟨13759620551024594664319511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 146769285877595676419408117 13759620551024594664319511)
              ·
                refine ⟨20639430826536891996479267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13759620551024594664319511 20639430826536891996479267)
                ·
                  refine ⟨30959146239805337994718901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20639430826536891996479267 30959146239805337994718901)
                  ·
                    refine ⟨2902419959981750437004897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30959146239805337994718901 2902419959981750437004897)
                    ·
                      refine ⟨2176814969986312827753673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2902419959981750437004897 2176814969986312827753673)
                      ·
                        rfl

theorem cell23_4239332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 1, 5, 2].length) (baseStart_4239332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4239332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4239332 prefixEnd_4239332 := by exact prefixLift 4239332
  have htrace : WordTrace (prefixWord ++ tailWord_4239332) baseStart_4239332 baseEnd_4239332 := by
    simpa [prefixWord, tailWord_4239332, baseEnd_4239332] using wordTrace_append hprefix tailTrace_4239332
  have hstable : (prefixWord ++ tailWord_4239332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4239332).length < 2 ^ (prefixWord ++ tailWord_4239332).sum := by decide
  have hdescent : baseEnd_4239332 < baseStart_4239332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4239332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4239365 : List Nat := [1, 3, 1, 1, 2, 4, 1, 1, 3, 1, 5]
def baseStart_4239365 : Nat := 118140960795 + 4239365 * 2 ^ 59
def prefixEnd_4239365 : Nat := 4983230072969 + 3 ^ 40 * 4239365 * 2
def baseEnd_4239365 : Nat := 2176831914847911198641021

theorem tailTrace_4239365 : CollatzResearch.WordTrace tailWord_4239365 prefixEnd_4239365 2176831914847911198641021 := by
  unfold tailWord_4239365
  simp only [CollatzResearch.WordTrace]
  refine ⟨154622344286512105744463549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103081562857674737162975699 154622344286512105744463549)
  ·
    refine ⟨57983379107442039654173831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154622344286512105744463549 57983379107442039654173831)
    ·
      refine ⟨86975068661163059481260747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57983379107442039654173831 86975068661163059481260747)
      ·
        refine ⟨130462602991744589221891121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86975068661163059481260747 130462602991744589221891121)
        ·
          refine ⟨97846952243808441916418341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130462602991744589221891121 97846952243808441916418341)
          ·
            refine ⟨18346303545714082859328439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 97846952243808441916418341 18346303545714082859328439)
            ·
              refine ⟨27519455318571124288992659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18346303545714082859328439 27519455318571124288992659)
              ·
                refine ⟨41279182977856686433488989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27519455318571124288992659 41279182977856686433488989)
                ·
                  refine ⟨15479693616696257412558371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41279182977856686433488989 15479693616696257412558371)
                  ·
                    refine ⟨23219540425044386118837557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15479693616696257412558371 23219540425044386118837557)
                    ·
                      refine ⟨2176831914847911198641021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23219540425044386118837557 2176831914847911198641021)
                      ·
                        rfl

theorem cell23_4239365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 1, 5].length) (baseStart_4239365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4239365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4239365 prefixEnd_4239365 := by exact prefixLift 4239365
  have htrace : WordTrace (prefixWord ++ tailWord_4239365) baseStart_4239365 baseEnd_4239365 := by
    simpa [prefixWord, tailWord_4239365, baseEnd_4239365] using wordTrace_append hprefix tailTrace_4239365
  have hstable : (prefixWord ++ tailWord_4239365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4239365).length < 2 ^ (prefixWord ++ tailWord_4239365).sum := by decide
  have hdescent : baseEnd_4239365 < baseStart_4239365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4239365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4239379 : List Nat := [1, 1, 1, 2, 1, 4, 4, 2, 3, 2, 2]
def baseStart_4239379 : Nat := 118140960795 + 4239379 * 2 ^ 59
def prefixEnd_4239379 : Nat := 4983230072969 + 3 ^ 40 * 4239379 * 2
def baseEnd_4239379 : Nat := 2176839103577074143865957

theorem tailTrace_4239379 : CollatzResearch.WordTrace tailWord_4239379 prefixEnd_4239379 2176839103577074143865957 := by
  unfold tailWord_4239379
  simp only [CollatzResearch.WordTrace]
  refine ⟨154622854908461386135473191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103081903272307590756982127 154622854908461386135473191)
  ·
    refine ⟨231934282362692079203209787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154622854908461386135473191 231934282362692079203209787)
    ·
      refine ⟨347901423544038118804814681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231934282362692079203209787 347901423544038118804814681)
      ·
        refine ⟨260926067658028589103611011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 347901423544038118804814681 260926067658028589103611011)
        ·
          refine ⟨391389101487042883655416517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260926067658028589103611011 391389101487042883655416517)
          ·
            refine ⟨73385456528820540685390597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 391389101487042883655416517 73385456528820540685390597)
            ·
              refine ⟨13759773099153851378510737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73385456528820540685390597 13759773099153851378510737)
              ·
                refine ⟨10319829824365388533883053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13759773099153851378510737 10319829824365388533883053)
                ·
                  refine ⟨3869936184137020700206145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10319829824365388533883053 3869936184137020700206145)
                  ·
                    refine ⟨2902452138102765525154609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3869936184137020700206145 2902452138102765525154609)
                    ·
                      refine ⟨2176839103577074143865957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2902452138102765525154609 2176839103577074143865957)
                      ·
                        rfl

theorem cell23_4239379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 3, 2, 2].length) (baseStart_4239379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4239379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4239379 prefixEnd_4239379 := by exact prefixLift 4239379
  have htrace : WordTrace (prefixWord ++ tailWord_4239379) baseStart_4239379 baseEnd_4239379 := by
    simpa [prefixWord, tailWord_4239379, baseEnd_4239379] using wordTrace_append hprefix tailTrace_4239379
  have hstable : (prefixWord ++ tailWord_4239379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4239379).length < 2 ^ (prefixWord ++ tailWord_4239379).sum := by decide
  have hdescent : baseEnd_4239379 < baseStart_4239379 := by decide
  rcases family_descends (prefixWord ++ tailWord_4239379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4239402 : List Nat := [3, 1, 4, 1, 2, 3, 9]
def baseStart_4239402 : Nat := 118140960795 + 4239402 * 2 ^ 59
def prefixEnd_4239402 : Nat := 4983230072969 + 3 ^ 40 * 4239402 * 2
def baseEnd_4239402 : Nat := 26874702637433673504671

theorem tailTrace_4239402 : CollatzResearch.WordTrace tailWord_4239402 prefixEnd_4239402 26874702637433673504671 := by
  unfold tailWord_4239402
  simp only [CollatzResearch.WordTrace]
  refine ⟨38655923446844515265890115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103082462524918707375706973 38655923446844515265890115)
  ·
    refine ⟨57983885170266772898835173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38655923446844515265890115 57983885170266772898835173)
    ·
      refine ⟨10871978469425019918531595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57983885170266772898835173 10871978469425019918531595)
      ·
        refine ⟨16307967704137529877797393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10871978469425019918531595 16307967704137529877797393)
        ·
          refine ⟨12230975778103147408348045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16307967704137529877797393 12230975778103147408348045)
          ·
            refine ⟨4586615916788680278130517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12230975778103147408348045 4586615916788680278130517)
            ·
              refine ⟨26874702637433673504671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4586615916788680278130517 26874702637433673504671)
              ·
                rfl

theorem cell23_4239402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 9].length) (baseStart_4239402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4239402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4239402 prefixEnd_4239402 := by exact prefixLift 4239402
  have htrace : WordTrace (prefixWord ++ tailWord_4239402) baseStart_4239402 baseEnd_4239402 := by
    simpa [prefixWord, tailWord_4239402, baseEnd_4239402] using wordTrace_append hprefix tailTrace_4239402
  have hstable : (prefixWord ++ tailWord_4239402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4239402).length < 2 ^ (prefixWord ++ tailWord_4239402).sum := by decide
  have hdescent : baseEnd_4239402 < baseStart_4239402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4239402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4239435 : List Nat := [1, 1, 1, 1, 3, 1, 2, 4, 2, 3, 4]
def baseStart_4239435 : Nat := 118140960795 + 4239435 * 2 ^ 59
def prefixEnd_4239435 : Nat := 4983230072969 + 3 ^ 40 * 4239435 * 2
def baseEnd_4239435 : Nat := 2176867858493725924765699

theorem tailTrace_4239435 : CollatzResearch.WordTrace tailWord_4239435 prefixEnd_4239435 2176867858493725924765699 := by
  unfold tailWord_4239435
  simp only [CollatzResearch.WordTrace]
  refine ⟨154624897396258507699511759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103083264930839005133007839 154624897396258507699511759)
  ·
    refine ⟨231937346094387761549267639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154624897396258507699511759 231937346094387761549267639)
    ·
      refine ⟨347906019141581642323901459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231937346094387761549267639 347906019141581642323901459)
      ·
        refine ⟨521859028712372463485852189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 347906019141581642323901459 521859028712372463485852189)
        ·
          refine ⟨195697135767139673807194571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 521859028712372463485852189 195697135767139673807194571)
          ·
            refine ⟨293545703650709510710791857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195697135767139673807194571 293545703650709510710791857)
            ·
              refine ⟨220159277738032133033093893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 293545703650709510710791857 220159277738032133033093893)
              ·
                refine ⟨41279864575881024943705105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 220159277738032133033093893 41279864575881024943705105)
                ·
                  refine ⟨30959898431910768707778829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41279864575881024943705105 30959898431910768707778829)
                  ·
                    refine ⟨11609961911966538265417061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30959898431910768707778829 11609961911966538265417061)
                    ·
                      refine ⟨2176867858493725924765699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11609961911966538265417061 2176867858493725924765699)
                      ·
                        rfl

theorem cell23_4239435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 3, 4].length) (baseStart_4239435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4239435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4239435 prefixEnd_4239435 := by exact prefixLift 4239435
  have htrace : WordTrace (prefixWord ++ tailWord_4239435) baseStart_4239435 baseEnd_4239435 := by
    simpa [prefixWord, tailWord_4239435, baseEnd_4239435] using wordTrace_append hprefix tailTrace_4239435
  have hstable : (prefixWord ++ tailWord_4239435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4239435).length < 2 ^ (prefixWord ++ tailWord_4239435).sum := by decide
  have hdescent : baseEnd_4239435 < baseStart_4239435 := by decide
  rcases family_descends (prefixWord ++ tailWord_4239435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4239446 : List Nat := [5, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3]
def baseStart_4239446 : Nat := 118140960795 + 4239446 * 2 ^ 59
def prefixEnd_4239446 : Nat := 4983230072969 + 3 ^ 40 * 4239446 * 2
def baseEnd_4239446 : Nat := 2176873506780925381728149

theorem tailTrace_4239446 : CollatzResearch.WordTrace tailWord_4239446 prefixEnd_4239446 2176873506780925381728149 := by
  unfold tailWord_4239446
  simp only [CollatzResearch.WordTrace]
  refine ⟨9664081162451166036135137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 103083532399479104385441461 9664081162451166036135137)
  ·
    refine ⟨7248060871838374527101353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9664081162451166036135137 7248060871838374527101353)
    ·
      refine ⟨5436045653878780895326015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7248060871838374527101353 5436045653878780895326015)
      ·
        refine ⟨8154068480818171342989023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5436045653878780895326015 8154068480818171342989023)
        ·
          refine ⟨12231102721227257014483535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8154068480818171342989023 12231102721227257014483535)
          ·
            refine ⟨18346654081840885521725303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12231102721227257014483535 18346654081840885521725303)
            ·
              refine ⟨27519981122761328282587955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18346654081840885521725303 27519981122761328282587955)
              ·
                refine ⟨41279971684141992423881933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27519981122761328282587955 41279971684141992423881933)
                ·
                  refine ⟨15479989381553247158955725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41279971684141992423881933 15479989381553247158955725)
                  ·
                    refine ⟨5804996018082467684608397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15479989381553247158955725 5804996018082467684608397)
                    ·
                      refine ⟨2176873506780925381728149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5804996018082467684608397 2176873506780925381728149)
                      ·
                        rfl

theorem cell23_4239446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_4239446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4239446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4239446 prefixEnd_4239446 := by exact prefixLift 4239446
  have htrace : WordTrace (prefixWord ++ tailWord_4239446) baseStart_4239446 baseEnd_4239446 := by
    simpa [prefixWord, tailWord_4239446, baseEnd_4239446] using wordTrace_append hprefix tailTrace_4239446
  have hstable : (prefixWord ++ tailWord_4239446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4239446).length < 2 ^ (prefixWord ++ tailWord_4239446).sum := by decide
  have hdescent : baseEnd_4239446 < baseStart_4239446 := by decide
  rcases family_descends (prefixWord ++ tailWord_4239446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4239455 : List Nat := [1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 5]
def baseStart_4239455 : Nat := 118140960795 + 4239455 * 2 ^ 59
def prefixEnd_4239455 : Nat := 4983230072969 + 3 ^ 40 * 4239455 * 2
def baseEnd_4239455 : Nat := 2176878128106815846515607

theorem tailTrace_4239455 : CollatzResearch.WordTrace tailWord_4239455 prefixEnd_4239455 2176878128106815846515607 := by
  unfold tailWord_4239455
  simp only [CollatzResearch.WordTrace]
  refine ⟨154625626856186051115239819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103083751237457367410159879 154625626856186051115239819)
  ·
    refine ⟨231938440284279076672859729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154625626856186051115239819 231938440284279076672859729)
    ·
      refine ⟨173953830213209307504644797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231938440284279076672859729 173953830213209307504644797)
      ·
        refine ⟨65232686329953490314241799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 173953830213209307504644797 65232686329953490314241799)
        ·
          refine ⟨97849029494930235471362699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65232686329953490314241799 97849029494930235471362699)
          ·
            refine ⟨146773544242395353207044049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97849029494930235471362699 146773544242395353207044049)
            ·
              refine ⟨110080158181796514905283037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146773544242395353207044049 110080158181796514905283037)
              ·
                refine ⟨41280059318173693089481139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110080158181796514905283037 41280059318173693089481139)
                ·
                  refine ⟨61920088977260539634221709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41280059318173693089481139 61920088977260539634221709)
                  ·
                    refine ⟨23220033366472702362833141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61920088977260539634221709 23220033366472702362833141)
                    ·
                      refine ⟨2176878128106815846515607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23220033366472702362833141 2176878128106815846515607)
                      ·
                        rfl

theorem cell23_4239455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_4239455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4239455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4239455 prefixEnd_4239455 := by exact prefixLift 4239455
  have htrace : WordTrace (prefixWord ++ tailWord_4239455) baseStart_4239455 baseEnd_4239455 := by
    simpa [prefixWord, tailWord_4239455, baseEnd_4239455] using wordTrace_append hprefix tailTrace_4239455
  have hstable : (prefixWord ++ tailWord_4239455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4239455).length < 2 ^ (prefixWord ++ tailWord_4239455).sum := by decide
  have hdescent : baseEnd_4239455 < baseStart_4239455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4239455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4239469 : List Nat := [1, 5, 1, 1, 2, 1, 1, 2, 3, 4, 2]
def baseStart_4239469 : Nat := 118140960795 + 4239469 * 2 ^ 59
def prefixEnd_4239469 : Nat := 4983230072969 + 3 ^ 40 * 4239469 * 2
def baseEnd_4239469 : Nat := 2176885316835978791740543

theorem tailTrace_4239469 : CollatzResearch.WordTrace tailWord_4239469 prefixEnd_4239469 2176885316835978791740543 := by
  unfold tailWord_4239469
  simp only [CollatzResearch.WordTrace]
  refine ⟨154626137478135331506249461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103084091652090221004166307 154626137478135331506249461)
  ·
    refine ⟨14496200388575187328710887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 154626137478135331506249461 14496200388575187328710887)
    ·
      refine ⟨21744300582862780993066331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14496200388575187328710887 21744300582862780993066331)
      ·
        refine ⟨32616450874294171489599497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21744300582862780993066331 32616450874294171489599497)
        ·
          refine ⟨24462338155720628617199623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32616450874294171489599497 24462338155720628617199623)
          ·
            refine ⟨36693507233580942925799435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24462338155720628617199623 36693507233580942925799435)
            ·
              refine ⟨55040260850371414388699153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36693507233580942925799435 55040260850371414388699153)
              ·
                refine ⟨41280195637778560791524365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55040260850371414388699153 41280195637778560791524365)
                ·
                  refine ⟨15480073364166960296821637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41280195637778560791524365 15480073364166960296821637)
                  ·
                    refine ⟨2902513755781305055654057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15480073364166960296821637 2902513755781305055654057)
                    ·
                      refine ⟨2176885316835978791740543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2902513755781305055654057 2176885316835978791740543)
                      ·
                        rfl

theorem cell23_4239469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 4, 2].length) (baseStart_4239469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4239469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4239469 prefixEnd_4239469 := by exact prefixLift 4239469
  have htrace : WordTrace (prefixWord ++ tailWord_4239469) baseStart_4239469 baseEnd_4239469 := by
    simpa [prefixWord, tailWord_4239469, baseEnd_4239469] using wordTrace_append hprefix tailTrace_4239469
  have hstable : (prefixWord ++ tailWord_4239469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4239469).length < 2 ^ (prefixWord ++ tailWord_4239469).sum := by decide
  have hdescent : baseEnd_4239469 < baseStart_4239469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4239469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4239472 : List Nat := [2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 3]
def baseStart_4239472 : Nat := 118140960795 + 4239472 * 2 ^ 59
def prefixEnd_4239472 : Nat := 4983230072969 + 3 ^ 40 * 4239472 * 2
def baseEnd_4239472 : Nat := 2176886857277942280003029

theorem tailTrace_4239472 : CollatzResearch.WordTrace tailWord_4239472 prefixEnd_4239472 2176886857277942280003029 := by
  unfold tailWord_4239472
  simp only [CollatzResearch.WordTrace]
  refine ⟨77313123448562231509304335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103084164598082975345739113 77313123448562231509304335)
  ·
    refine ⟨115969685172843347263956503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77313123448562231509304335 115969685172843347263956503)
    ·
      refine ⟨173954527759265020895934755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115969685172843347263956503 173954527759265020895934755)
      ·
        refine ⟨260931791638897531343902133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173954527759265020895934755 260931791638897531343902133)
        ·
          refine ⟨24462355466146643563490825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 260931791638897531343902133 24462355466146643563490825)
          ·
            refine ⟨18346766599609982672618119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24462355466146643563490825 18346766599609982672618119)
            ·
              refine ⟨27520149899414974008927179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18346766599609982672618119 27520149899414974008927179)
              ·
                refine ⟨41280224849122461013390769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27520149899414974008927179 41280224849122461013390769)
                ·
                  refine ⟨30960168636841845760043077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41280224849122461013390769 30960168636841845760043077)
                  ·
                    refine ⟨5805031619407846080008077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30960168636841845760043077 5805031619407846080008077)
                    ·
                      refine ⟨2176886857277942280003029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5805031619407846080008077 2176886857277942280003029)
                      ·
                        rfl

theorem cell23_4239472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 3].length) (baseStart_4239472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4239472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4239472 prefixEnd_4239472 := by exact prefixLift 4239472
  have htrace : WordTrace (prefixWord ++ tailWord_4239472) baseStart_4239472 baseEnd_4239472 := by
    simpa [prefixWord, tailWord_4239472, baseEnd_4239472] using wordTrace_append hprefix tailTrace_4239472
  have hstable : (prefixWord ++ tailWord_4239472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4239472).length < 2 ^ (prefixWord ++ tailWord_4239472).sum := by decide
  have hdescent : baseEnd_4239472 < baseStart_4239472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4239472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4239492 : List Nat := [2, 3, 2, 1, 2, 1, 3, 2, 7]
def baseStart_4239492 : Nat := 118140960795 + 4239492 * 2 ^ 59
def prefixEnd_4239492 : Nat := 4983230072969 + 3 ^ 40 * 4239492 * 2
def baseEnd_4239492 : Nat := 241877458543448022416993

theorem tailTrace_4239492 : CollatzResearch.WordTrace tailWord_4239492 prefixEnd_4239492 241877458543448022416993 := by
  unfold tailWord_4239492
  simp only [CollatzResearch.WordTrace]
  refine ⟨77313488178526003217168365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103084650904701337622891153 77313488178526003217168365)
  ·
    refine ⟨28992558066947251206438137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77313488178526003217168365 28992558066947251206438137)
    ·
      refine ⟨21744418550210438404828603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28992558066947251206438137 21744418550210438404828603)
      ·
        refine ⟨32616627825315657607242905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21744418550210438404828603 32616627825315657607242905)
        ·
          refine ⟨24462470868986743205432179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32616627825315657607242905 24462470868986743205432179)
          ·
            refine ⟨36693706303480114808148269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24462470868986743205432179 36693706303480114808148269)
            ·
              refine ⟨13760139863805043053055601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36693706303480114808148269 13760139863805043053055601)
              ·
                refine ⟨10320104897853782289791701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13760139863805043053055601 10320104897853782289791701)
                ·
                  refine ⟨241877458543448022416993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10320104897853782289791701 241877458543448022416993)
                  ·
                    rfl

theorem cell23_4239492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 7].length) (baseStart_4239492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4239492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4239492 prefixEnd_4239492 := by exact prefixLift 4239492
  have htrace : WordTrace (prefixWord ++ tailWord_4239492) baseStart_4239492 baseEnd_4239492 := by
    simpa [prefixWord, tailWord_4239492, baseEnd_4239492] using wordTrace_append hprefix tailTrace_4239492
  have hstable : (prefixWord ++ tailWord_4239492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4239492).length < 2 ^ (prefixWord ++ tailWord_4239492).sum := by decide
  have hdescent : baseEnd_4239492 < baseStart_4239492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4239492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4239509 : List Nat := [1, 3, 2, 1, 1, 1, 6, 3, 5]
def baseStart_4239509 : Nat := 118140960795 + 4239509 * 2 ^ 59
def prefixEnd_4239509 : Nat := 4983230072969 + 3 ^ 40 * 4239509 * 2
def baseEnd_4239509 : Nat := 241878428451350959471151

theorem tailTrace_4239509 : CollatzResearch.WordTrace tailWord_4239509 prefixEnd_4239509 241878428451350959471151 := by
  unfold tailWord_4239509
  simp only [CollatzResearch.WordTrace]
  refine ⟨154627596397990418337705581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103085064265326945558470387 154627596397990418337705581)
  ·
    refine ⟨57985348649246406876639593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154627596397990418337705581 57985348649246406876639593)
    ·
      refine ⟨43489011486934805157479695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57985348649246406876639593 43489011486934805157479695)
      ·
        refine ⟨65233517230402207736219543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43489011486934805157479695 65233517230402207736219543)
        ·
          refine ⟨97850275845603311604329315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65233517230402207736219543 97850275845603311604329315)
          ·
            refine ⟨146775413768404967406493973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97850275845603311604329315 146775413768404967406493973)
            ·
              refine ⟨6880097520393982847179405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 146775413768404967406493973 6880097520393982847179405)
              ·
                refine ⟨2580036570147743567692277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6880097520393982847179405 2580036570147743567692277)
                ·
                  refine ⟨241878428451350959471151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2580036570147743567692277 241878428451350959471151)
                  ·
                    rfl

theorem cell23_4239509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 3, 5].length) (baseStart_4239509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4239509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4239509 prefixEnd_4239509 := by exact prefixLift 4239509
  have htrace : WordTrace (prefixWord ++ tailWord_4239509) baseStart_4239509 baseEnd_4239509 := by
    simpa [prefixWord, tailWord_4239509, baseEnd_4239509] using wordTrace_append hprefix tailTrace_4239509
  have hstable : (prefixWord ++ tailWord_4239509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4239509).length < 2 ^ (prefixWord ++ tailWord_4239509).sum := by decide
  have hdescent : baseEnd_4239509 < baseStart_4239509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4239509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4239515 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 7]
def baseStart_4239515 : Nat := 118140960795 + 4239515 * 2 ^ 59
def prefixEnd_4239515 : Nat := 4983230072969 + 3 ^ 40 * 4239515 * 2
def baseEnd_4239515 : Nat := 2176908936946085611765331

theorem tailTrace_4239515 : CollatzResearch.WordTrace tailWord_4239515 prefixEnd_4239515 2176908936946085611765331 := by
  unfold tailWord_4239515
  simp only [CollatzResearch.WordTrace]
  refine ⟨154627815235968681362423999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103085210157312454241615999 154627815235968681362423999)
  ·
    refine ⟨231941722853953022043635999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154627815235968681362423999 231941722853953022043635999)
    ·
      refine ⟨347912584280929533065453999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231941722853953022043635999 347912584280929533065453999)
      ·
        refine ⟨521868876421394299598180999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 347912584280929533065453999 521868876421394299598180999)
        ·
          refine ⟨782803314632091449397271499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 521868876421394299598180999 782803314632091449397271499)
          ·
            refine ⟨1174204971948137174095907249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 782803314632091449397271499 1174204971948137174095907249)
            ·
              refine ⟨880653728961102880571930437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1174204971948137174095907249 880653728961102880571930437)
              ·
                refine ⟨165122574180206790107236957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 880653728961102880571930437 165122574180206790107236957)
                ·
                  refine ⟨61920965317577546290213859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 165122574180206790107236957 61920965317577546290213859)
                  ·
                    refine ⟨92881447976366319435320789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61920965317577546290213859 92881447976366319435320789)
                    ·
                      refine ⟨2176908936946085611765331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 92881447976366319435320789 2176908936946085611765331)
                      ·
                        rfl

theorem cell23_4239515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 7].length) (baseStart_4239515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4239515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4239515 prefixEnd_4239515 := by exact prefixLift 4239515
  have htrace : WordTrace (prefixWord ++ tailWord_4239515) baseStart_4239515 baseEnd_4239515 := by
    simpa [prefixWord, tailWord_4239515, baseEnd_4239515] using wordTrace_append hprefix tailTrace_4239515
  have hstable : (prefixWord ++ tailWord_4239515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4239515).length < 2 ^ (prefixWord ++ tailWord_4239515).sum := by decide
  have hdescent : baseEnd_4239515 < baseStart_4239515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4239515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4239519 : List Nat := [1, 1, 2, 6, 1, 1, 1, 2, 2, 3, 3]
def baseStart_4239519 : Nat := 118140960795 + 4239519 * 2 ^ 59
def prefixEnd_4239519 : Nat := 4983230072969 + 3 ^ 40 * 4239519 * 2
def baseEnd_4239519 : Nat := 2176910990868703596115313

theorem tailTrace_4239519 : CollatzResearch.WordTrace tailWord_4239519 prefixEnd_4239519 2176910990868703596115313 := by
  unfold tailWord_4239519
  simp only [CollatzResearch.WordTrace]
  refine ⟨154627961127954190045569611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103085307418636126697046407 154627961127954190045569611)
  ·
    refine ⟨231941941691931285068354417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154627961127954190045569611 231941941691931285068354417)
    ·
      refine ⟨173956456268948463801265813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231941941691931285068354417 173956456268948463801265813)
      ·
        refine ⟨8154208887606959240684335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 173956456268948463801265813 8154208887606959240684335)
        ·
          refine ⟨12231313331410438861026503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8154208887606959240684335 12231313331410438861026503)
          ·
            refine ⟨18346969997115658291539755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12231313331410438861026503 18346969997115658291539755)
            ·
              refine ⟨27520454995673487437309633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18346969997115658291539755 27520454995673487437309633)
              ·
                refine ⟨20640341246755115577982225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27520454995673487437309633 20640341246755115577982225)
                ·
                  refine ⟨15480255935066336683486669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20640341246755115577982225 15480255935066336683486669)
                  ·
                    refine ⟨5805095975649876256307501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15480255935066336683486669 5805095975649876256307501)
                    ·
                      refine ⟨2176910990868703596115313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5805095975649876256307501 2176910990868703596115313)
                      ·
                        rfl

theorem cell23_4239519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_4239519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4239519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4239519 prefixEnd_4239519 := by exact prefixLift 4239519
  have htrace : WordTrace (prefixWord ++ tailWord_4239519) baseStart_4239519 baseEnd_4239519 := by
    simpa [prefixWord, tailWord_4239519, baseEnd_4239519] using wordTrace_append hprefix tailTrace_4239519
  have hstable : (prefixWord ++ tailWord_4239519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4239519).length < 2 ^ (prefixWord ++ tailWord_4239519).sum := by decide
  have hdescent : baseEnd_4239519 < baseStart_4239519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4239519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4239599 : List Nat := [1, 1, 2, 1, 6, 2, 1, 3, 6]
def baseStart_4239599 : Nat := 118140960795 + 4239599 * 2 ^ 59
def prefixEnd_4239599 : Nat := 4983230072969 + 3 ^ 40 * 4239599 * 2
def baseEnd_4239599 : Nat := 241883563257895920346105

theorem tailTrace_4239599 : CollatzResearch.WordTrace tailWord_4239599 prefixEnd_4239599 241883563257895920346105 := by
  unfold tailWord_4239599
  simp only [CollatzResearch.WordTrace]
  refine ⟨154630878967664363708481851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103087252645109575805654567 154630878967664363708481851)
  ·
    refine ⟨231946318451496545562722777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154630878967664363708481851 231946318451496545562722777)
    ·
      refine ⟨173959738838622409172042083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231946318451496545562722777 173959738838622409172042083)
      ·
        refine ⟨260939608257933613758063125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173959738838622409172042083 260939608257933613758063125)
        ·
          refine ⟨12231544137090638144909209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 260939608257933613758063125 12231544137090638144909209)
          ·
            refine ⟨9173658102817978608681907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12231544137090638144909209 9173658102817978608681907)
            ·
              refine ⟨13760487154226967913022861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9173658102817978608681907 13760487154226967913022861)
              ·
                refine ⟨5160182682835112967383573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13760487154226967913022861 5160182682835112967383573)
                ·
                  refine ⟨241883563257895920346105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5160182682835112967383573 241883563257895920346105)
                  ·
                    rfl

theorem cell23_4239599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 3, 6].length) (baseStart_4239599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4239599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4239599 prefixEnd_4239599 := by exact prefixLift 4239599
  have htrace : WordTrace (prefixWord ++ tailWord_4239599) baseStart_4239599 baseEnd_4239599 := by
    simpa [prefixWord, tailWord_4239599, baseEnd_4239599] using wordTrace_append hprefix tailTrace_4239599
  have hstable : (prefixWord ++ tailWord_4239599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4239599).length < 2 ^ (prefixWord ++ tailWord_4239599).sum := by decide
  have hdescent : baseEnd_4239599 < baseStart_4239599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4239599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4239649 : List Nat := [1, 2, 3, 2, 1, 1, 3, 2, 3, 1, 4]
def baseStart_4239649 : Nat := 118140960795 + 4239649 * 2 ^ 59
def prefixEnd_4239649 : Nat := 4983230072969 + 3 ^ 40 * 4239649 * 2
def baseEnd_4239649 : Nat := 2176977743353788087489715

theorem tailTrace_4239649 : CollatzResearch.WordTrace tailWord_4239649 prefixEnd_4239649 2176977743353788087489715 := by
  unfold tailWord_4239649
  simp only [CollatzResearch.WordTrace]
  refine ⟨154632702617483222247802001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103088468411655481498534667 154632702617483222247802001)
  ·
    refine ⟨115974526963112416685851501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154632702617483222247802001 115974526963112416685851501)
    ·
      refine ⟨43490447611167156257194313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115974526963112416685851501 43490447611167156257194313)
      ·
        refine ⟨32617835708375367192895735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43490447611167156257194313 32617835708375367192895735)
        ·
          refine ⟨48926753562563050789343603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32617835708375367192895735 48926753562563050789343603)
          ·
            refine ⟨73390130343844576184015405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48926753562563050789343603 73390130343844576184015405)
            ·
              refine ⟨27521298878941716069005777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73390130343844576184015405 27521298878941716069005777)
              ·
                refine ⟨20640974159206287051754333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27521298878941716069005777 20640974159206287051754333)
                ·
                  refine ⟨7740365309702357644407875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20640974159206287051754333 7740365309702357644407875)
                  ·
                    refine ⟨11610547964553536466611813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7740365309702357644407875 11610547964553536466611813)
                    ·
                      refine ⟨2176977743353788087489715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11610547964553536466611813 2176977743353788087489715)
                      ·
                        rfl

theorem cell23_4239649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_4239649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4239649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4239649 prefixEnd_4239649 := by exact prefixLift 4239649
  have htrace : WordTrace (prefixWord ++ tailWord_4239649) baseStart_4239649 baseEnd_4239649 := by
    simpa [prefixWord, tailWord_4239649, baseEnd_4239649] using wordTrace_append hprefix tailTrace_4239649
  have hstable : (prefixWord ++ tailWord_4239649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4239649).length < 2 ^ (prefixWord ++ tailWord_4239649).sum := by decide
  have hdescent : baseEnd_4239649 < baseStart_4239649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4239649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4239672 : List Nat := [2, 1, 2, 1, 3, 1, 2, 11]
def baseStart_4239672 : Nat := 118140960795 + 4239672 * 2 ^ 59
def prefixEnd_4239672 : Nat := 4983230072969 + 3 ^ 40 * 4239672 * 2
def baseEnd_4239672 : Nat := 80629242718845981388967

theorem tailTrace_4239672 : CollatzResearch.WordTrace tailWord_4239672 prefixEnd_4239672 80629242718845981388967 := by
  unfold tailWord_4239672
  simp only [CollatzResearch.WordTrace]
  refine ⟨77316770748199948587944635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103089027664266598117259513 77316770748199948587944635)
  ·
    refine ⟨115975156122299922881916953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77316770748199948587944635 115975156122299922881916953)
    ·
      refine ⟨86981367091724942161437715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115975156122299922881916953 86981367091724942161437715)
      ·
        refine ⟨130472050637587413242156573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86981367091724942161437715 130472050637587413242156573)
        ·
          refine ⟨48927018989095279965808715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130472050637587413242156573 48927018989095279965808715)
          ·
            refine ⟨73390528483642919948713073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48927018989095279965808715 73390528483642919948713073)
            ·
              refine ⟨55042896362732189961534805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73390528483642919948713073 55042896362732189961534805)
              ·
                refine ⟨80629242718845981388967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 55042896362732189961534805 80629242718845981388967)
                ·
                  rfl

theorem cell23_4239672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 11].length) (baseStart_4239672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4239672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4239672 prefixEnd_4239672 := by exact prefixLift 4239672
  have htrace : WordTrace (prefixWord ++ tailWord_4239672) baseStart_4239672 baseEnd_4239672 := by
    simpa [prefixWord, tailWord_4239672, baseEnd_4239672] using wordTrace_append hprefix tailTrace_4239672
  have hstable : (prefixWord ++ tailWord_4239672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4239672).length < 2 ^ (prefixWord ++ tailWord_4239672).sum := by decide
  have hdescent : baseEnd_4239672 < baseStart_4239672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4239672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4239679 : List Nat := [1, 1, 2, 2, 4, 1, 1, 4, 1, 2, 4]
def baseStart_4239679 : Nat := 118140960795 + 4239679 * 2 ^ 59
def prefixEnd_4239679 : Nat := 4983230072969 + 3 ^ 40 * 4239679 * 2
def baseEnd_4239679 : Nat := 2176993147773422970114577

theorem tailTrace_4239679 : CollatzResearch.WordTrace tailWord_4239679 prefixEnd_4239679 2176993147773422970114577 := by
  unfold tailWord_4239679
  simp only [CollatzResearch.WordTrace]
  refine ⟨154633796807374537371394091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103089197871583024914262727 154633796807374537371394091)
  ·
    refine ⟨231950695211061806057091137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154633796807374537371394091 231950695211061806057091137)
    ·
      refine ⟨173963021408296354542818353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231950695211061806057091137 173963021408296354542818353)
      ·
        refine ⟨130472266056222265907113765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173963021408296354542818353 130472266056222265907113765)
        ·
          refine ⟨24463549885541674857583831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 130472266056222265907113765 24463549885541674857583831)
          ·
            refine ⟨36695324828312512286375747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24463549885541674857583831 36695324828312512286375747)
            ·
              refine ⟨55042987242468768429563621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36695324828312512286375747 55042987242468768429563621)
              ·
                refine ⟨10320560107962894080543179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55042987242468768429563621 10320560107962894080543179)
                ·
                  refine ⟨15480840161944341120814769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10320560107962894080543179 15480840161944341120814769)
                  ·
                    refine ⟨11610630121458255840611077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15480840161944341120814769 11610630121458255840611077)
                    ·
                      refine ⟨2176993147773422970114577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11610630121458255840611077 2176993147773422970114577)
                      ·
                        rfl

theorem cell23_4239679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 2, 4].length) (baseStart_4239679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4239679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4239679 prefixEnd_4239679 := by exact prefixLift 4239679
  have htrace : WordTrace (prefixWord ++ tailWord_4239679) baseStart_4239679 baseEnd_4239679 := by
    simpa [prefixWord, tailWord_4239679, baseEnd_4239679] using wordTrace_append hprefix tailTrace_4239679
  have hstable : (prefixWord ++ tailWord_4239679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4239679).length < 2 ^ (prefixWord ++ tailWord_4239679).sum := by decide
  have hdescent : baseEnd_4239679 < baseStart_4239679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4239679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4239700 : List Nat := [2, 4, 1, 1, 2, 3, 2, 1, 3, 2, 2]
def baseStart_4239700 : Nat := 118140960795 + 4239700 * 2 ^ 59
def prefixEnd_4239700 : Nat := 4983230072969 + 3 ^ 40 * 4239700 * 2
def baseEnd_4239700 : Nat := 2177003930867167387951981

theorem tailTrace_4239700 : CollatzResearch.WordTrace tailWord_4239700 prefixEnd_4239700 2177003930867167387951981 := by
  unfold tailWord_4239700
  simp only [CollatzResearch.WordTrace]
  refine ⟨77317281370149228978954277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103089708493532305305272369 77317281370149228978954277)
  ·
    refine ⟨14496990256902980433553927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77317281370149228978954277 14496990256902980433553927)
    ·
      refine ⟨21745485385354470650330891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14496990256902980433553927 21745485385354470650330891)
      ·
        refine ⟨32618228078031705975496337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21745485385354470650330891 32618228078031705975496337)
        ·
          refine ⟨24463671058523779481622253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32618228078031705975496337 24463671058523779481622253)
          ·
            refine ⟨9173876646946417305608345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24463671058523779481622253 9173876646946417305608345)
            ·
              refine ⟨6880407485209812979206259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9173876646946417305608345 6880407485209812979206259)
              ·
                refine ⟨10320611227814719468809389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6880407485209812979206259 10320611227814719468809389)
                ·
                  refine ⟨3870229210430519800803521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10320611227814719468809389 3870229210430519800803521)
                  ·
                    refine ⟨2902671907822889850602641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3870229210430519800803521 2902671907822889850602641)
                    ·
                      refine ⟨2177003930867167387951981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2902671907822889850602641 2177003930867167387951981)
                      ·
                        rfl

theorem cell23_4239700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 3, 2, 2].length) (baseStart_4239700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4239700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4239700 prefixEnd_4239700 := by exact prefixLift 4239700
  have htrace : WordTrace (prefixWord ++ tailWord_4239700) baseStart_4239700 baseEnd_4239700 := by
    simpa [prefixWord, tailWord_4239700, baseEnd_4239700] using wordTrace_append hprefix tailTrace_4239700
  have hstable : (prefixWord ++ tailWord_4239700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4239700).length < 2 ^ (prefixWord ++ tailWord_4239700).sum := by decide
  have hdescent : baseEnd_4239700 < baseStart_4239700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4239700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4239733 : List Nat := [1, 3, 4, 1, 2, 1, 1, 2, 4, 1, 3]
def baseStart_4239733 : Nat := 118140960795 + 4239733 * 2 ^ 59
def prefixEnd_4239733 : Nat := 4983230072969 + 3 ^ 40 * 4239733 * 2
def baseEnd_4239733 : Nat := 2177020875728765758839329

theorem tailTrace_4239733 : CollatzResearch.WordTrace tailWord_4239733 prefixEnd_4239733 2177020875728765758839329 := by
  unfold tailWord_4239733
  simp only [CollatzResearch.WordTrace]
  refine ⟨154635766349178904593859853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103090510899452603062573235 154635766349178904593859853)
  ·
    refine ⟨57988412380942089222697445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154635766349178904593859853 57988412380942089222697445)
    ·
      refine ⟨10872827321426641729255771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57988412380942089222697445 10872827321426641729255771)
      ·
        refine ⟨16309240982139962593883657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10872827321426641729255771 16309240982139962593883657)
        ·
          refine ⟨12231930736604971945412743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16309240982139962593883657 12231930736604971945412743)
          ·
            refine ⟨18347896104907457918119115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12231930736604971945412743 18347896104907457918119115)
            ·
              refine ⟨27521844157361186877178673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18347896104907457918119115 27521844157361186877178673)
              ·
                refine ⟨20641383118020890157884005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27521844157361186877178673 20641383118020890157884005)
                ·
                  refine ⟨3870259334628916904603251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20641383118020890157884005 3870259334628916904603251)
                  ·
                    refine ⟨5805389001943375356904877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3870259334628916904603251 5805389001943375356904877)
                    ·
                      refine ⟨2177020875728765758839329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5805389001943375356904877 2177020875728765758839329)
                      ·
                        rfl

theorem cell23_4239733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_4239733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4239733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4239733 prefixEnd_4239733 := by exact prefixLift 4239733
  have htrace : WordTrace (prefixWord ++ tailWord_4239733) baseStart_4239733 baseEnd_4239733 := by
    simpa [prefixWord, tailWord_4239733, baseEnd_4239733] using wordTrace_append hprefix tailTrace_4239733
  have hstable : (prefixWord ++ tailWord_4239733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4239733).length < 2 ^ (prefixWord ++ tailWord_4239733).sum := by decide
  have hdescent : baseEnd_4239733 < baseStart_4239733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4239733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4239769 : List Nat := [1, 2, 1, 2, 1, 4, 2, 1, 1, 4, 4]
def baseStart_4239769 : Nat := 118140960795 + 4239769 * 2 ^ 59
def prefixEnd_4239769 : Nat := 4983230072969 + 3 ^ 40 * 4239769 * 2
def baseEnd_4239769 : Nat := 2177039361032327617989163

theorem tailTrace_4239769 : CollatzResearch.WordTrace tailWord_4239769 prefixEnd_4239769 2177039361032327617989163 := by
  unfold tailWord_4239769
  simp only [CollatzResearch.WordTrace]
  refine ⟨154637079377048482742170361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103091386251365655161446907 154637079377048482742170361)
  ·
    refine ⟨115977809532786362056627771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154637079377048482742170361 115977809532786362056627771)
    ·
      refine ⟨173966714299179543084941657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115977809532786362056627771 173966714299179543084941657)
      ·
        refine ⟨130475035724384657313706243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173966714299179543084941657 130475035724384657313706243)
        ·
          refine ⟨195712553586576985970559365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130475035724384657313706243 195712553586576985970559365)
          ·
            refine ⟨36696103797483184869479881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 195712553586576985970559365 36696103797483184869479881)
            ·
              refine ⟨27522077848112388652109911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36696103797483184869479881 27522077848112388652109911)
              ·
                refine ⟨41283116772168582978164867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27522077848112388652109911 41283116772168582978164867)
                ·
                  refine ⟨61924675158252874467247301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41283116772168582978164867 61924675158252874467247301)
                  ·
                    refine ⟨11610876592172413962608869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61924675158252874467247301 11610876592172413962608869)
                    ·
                      refine ⟨2177039361032327617989163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11610876592172413962608869 2177039361032327617989163)
                      ·
                        rfl

theorem cell23_4239769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 4, 4].length) (baseStart_4239769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4239769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4239769 prefixEnd_4239769 := by exact prefixLift 4239769
  have htrace : WordTrace (prefixWord ++ tailWord_4239769) baseStart_4239769 baseEnd_4239769 := by
    simpa [prefixWord, tailWord_4239769, baseEnd_4239769] using wordTrace_append hprefix tailTrace_4239769
  have hstable : (prefixWord ++ tailWord_4239769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4239769).length < 2 ^ (prefixWord ++ tailWord_4239769).sum := by decide
  have hdescent : baseEnd_4239769 < baseStart_4239769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4239769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4239849 : List Nat := [1, 2, 1, 1, 1, 2, 1, 4, 2, 3, 5]
def baseStart_4239849 : Nat := 118140960795 + 4239849 * 2 ^ 59
def prefixEnd_4239849 : Nat := 4983230072969 + 3 ^ 40 * 4239849 * 2
def baseEnd_4239849 : Nat := 2177080439484687304988795

theorem tailTrace_4239849 : CollatzResearch.WordTrace tailWord_4239849 prefixEnd_4239849 2177080439484687304988795 := by
  unfold tailWord_4239849
  simp only [CollatzResearch.WordTrace]
  refine ⟨154639997216758656405082601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103093331477839104270055067 154639997216758656405082601)
  ·
    refine ⟨115979997912568992303811951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154639997216758656405082601 115979997912568992303811951)
    ·
      refine ⟨173969996868853488455717927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115979997912568992303811951 173969996868853488455717927)
      ·
        refine ⟨260954995303280232683576891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173969996868853488455717927 260954995303280232683576891)
        ·
          refine ⟨391432492954920349025365337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260954995303280232683576891 391432492954920349025365337)
          ·
            refine ⟨293574369716190261769024003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 391432492954920349025365337 293574369716190261769024003)
            ·
              refine ⟨440361554574285392653536005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 293574369716190261769024003 440361554574285392653536005)
              ·
                refine ⟨82567791482678511122538001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 440361554574285392653536005 82567791482678511122538001)
                ·
                  refine ⟨61925843612008883341903501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82567791482678511122538001 61925843612008883341903501)
                  ·
                    refine ⟨23222191354503331253213813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61925843612008883341903501 23222191354503331253213813)
                    ·
                      refine ⟨2177080439484687304988795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23222191354503331253213813 2177080439484687304988795)
                      ·
                        rfl

theorem cell23_4239849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 3, 5].length) (baseStart_4239849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4239849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4239849 prefixEnd_4239849 := by exact prefixLift 4239849
  have htrace : WordTrace (prefixWord ++ tailWord_4239849) baseStart_4239849 baseEnd_4239849 := by
    simpa [prefixWord, tailWord_4239849, baseEnd_4239849] using wordTrace_append hprefix tailTrace_4239849
  have hstable : (prefixWord ++ tailWord_4239849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4239849).length < 2 ^ (prefixWord ++ tailWord_4239849).sum := by decide
  have hdescent : baseEnd_4239849 < baseStart_4239849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4239849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4239856 : List Nat := [2, 1, 1, 1, 3, 3, 1, 2, 5, 4]
def baseStart_4239856 : Nat := 118140960795 + 4239856 * 2 ^ 59
def prefixEnd_4239856 : Nat := 4983230072969 + 3 ^ 40 * 4239856 * 2
def baseEnd_4239856 : Nat := 725694677949756259200421

theorem tailTrace_4239856 : CollatzResearch.WordTrace tailWord_4239856 prefixEnd_4239856 725694677949756259200421 := by
  unfold tailWord_4239856
  simp only [CollatzResearch.WordTrace]
  refine ⟨77320126263866648300293711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103093501685155531067058281 77320126263866648300293711)
  ·
    refine ⟨115980189395799972450440567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77320126263866648300293711 115980189395799972450440567)
    ·
      refine ⟨173970284093699958675660851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115980189395799972450440567 173970284093699958675660851)
      ·
        refine ⟨260955426140549938013491277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173970284093699958675660851 260955426140549938013491277)
        ·
          refine ⟨97858284802706226755059229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 260955426140549938013491277 97858284802706226755059229)
          ·
            refine ⟨36696856801014835033147211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97858284802706226755059229 36696856801014835033147211)
            ·
              refine ⟨55045285201522252549720817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36696856801014835033147211 55045285201522252549720817)
              ·
                refine ⟨41283963901141689412290613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55045285201522252549720817 41283963901141689412290613)
                ·
                  refine ⟨3870371615732033382402245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41283963901141689412290613 3870371615732033382402245)
                  ·
                    refine ⟨725694677949756259200421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3870371615732033382402245 725694677949756259200421)
                    ·
                      rfl

theorem cell23_4239856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 5, 4].length) (baseStart_4239856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4239856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4239856 prefixEnd_4239856 := by exact prefixLift 4239856
  have htrace : WordTrace (prefixWord ++ tailWord_4239856) baseStart_4239856 baseEnd_4239856 := by
    simpa [prefixWord, tailWord_4239856, baseEnd_4239856] using wordTrace_append hprefix tailTrace_4239856
  have hstable : (prefixWord ++ tailWord_4239856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4239856).length < 2 ^ (prefixWord ++ tailWord_4239856).sum := by decide
  have hdescent : baseEnd_4239856 < baseStart_4239856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4239856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4239859 : List Nat := [1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 6]
def baseStart_4239859 : Nat := 118140960795 + 4239859 * 2 ^ 59
def prefixEnd_4239859 : Nat := 4983230072969 + 3 ^ 40 * 4239859 * 2
def baseEnd_4239859 : Nat := 2177085574291232265863749

theorem tailTrace_4239859 : CollatzResearch.WordTrace tailWord_4239859 prefixEnd_4239859 2177085574291232265863749 := by
  unfold tailWord_4239859
  simp only [CollatzResearch.WordTrace]
  refine ⟨154640361946722428112946631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103093574631148285408631087 154640361946722428112946631)
  ·
    refine ⟨231960542920083642169419947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154640361946722428112946631 231960542920083642169419947)
    ·
      refine ⟨347940814380125463254129921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231960542920083642169419947 347940814380125463254129921)
      ·
        refine ⟨260955610785094097440597441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 347940814380125463254129921 260955610785094097440597441)
        ·
          refine ⟨195716708088820573080448081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 260955610785094097440597441 195716708088820573080448081)
          ·
            refine ⟨146787531066615429810336061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 195716708088820573080448081 146787531066615429810336061)
            ·
              refine ⟨55045324149980786178876023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 146787531066615429810336061 55045324149980786178876023)
              ·
                refine ⟨82567986224971179268314035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55045324149980786178876023 82567986224971179268314035)
                ·
                  refine ⟨123851979337456768902471053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82567986224971179268314035 123851979337456768902471053)
                  ·
                    refine ⟨46444492251546288338426645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 123851979337456768902471053 46444492251546288338426645)
                    ·
                      refine ⟨2177085574291232265863749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46444492251546288338426645 2177085574291232265863749)
                      ·
                        rfl

theorem cell23_4239859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 6].length) (baseStart_4239859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4239859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4239859 prefixEnd_4239859 := by exact prefixLift 4239859
  have htrace : WordTrace (prefixWord ++ tailWord_4239859) baseStart_4239859 baseEnd_4239859 := by
    simpa [prefixWord, tailWord_4239859, baseEnd_4239859] using wordTrace_append hprefix tailTrace_4239859
  have hstable : (prefixWord ++ tailWord_4239859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4239859).length < 2 ^ (prefixWord ++ tailWord_4239859).sum := by decide
  have hdescent : baseEnd_4239859 < baseStart_4239859 := by decide
  rcases family_descends (prefixWord ++ tailWord_4239859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4239873 : List Nat := [1, 2, 4, 1, 3, 1, 1, 3, 3, 4]
def baseStart_4239873 : Nat := 118140960795 + 4239873 * 2 ^ 59
def prefixEnd_4239873 : Nat := 4983230072969 + 3 ^ 40 * 4239873 * 2
def baseEnd_4239873 : Nat := 725697587673465070362895

theorem tailTrace_4239873 : CollatzResearch.WordTrace tailWord_4239873 prefixEnd_4239873 725697587673465070362895 := by
  unfold tailWord_4239873
  simp only [CollatzResearch.WordTrace]
  refine ⟨154640872568671708503956273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103093915045781139002637515 154640872568671708503956273)
  ·
    refine ⟨115980654426503781377967205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154640872568671708503956273 115980654426503781377967205)
    ·
      refine ⟨21746372704969459008368851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115980654426503781377967205 21746372704969459008368851)
      ·
        refine ⟨32619559057454188512553277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21746372704969459008368851 32619559057454188512553277)
        ·
          refine ⟨12232334646545320692207479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32619559057454188512553277 12232334646545320692207479)
          ·
            refine ⟨18348501969817981038311219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12232334646545320692207479 18348501969817981038311219)
            ·
              refine ⟨27522752954726971557466829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18348501969817981038311219 27522752954726971557466829)
              ·
                refine ⟨10321032358022614334050061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27522752954726971557466829 10321032358022614334050061)
                ·
                  refine ⟨3870387134258480375268773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10321032358022614334050061 3870387134258480375268773)
                  ·
                    refine ⟨725697587673465070362895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3870387134258480375268773 725697587673465070362895)
                    ·
                      rfl

theorem cell23_4239873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_4239873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4239873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4239873 prefixEnd_4239873 := by exact prefixLift 4239873
  have htrace : WordTrace (prefixWord ++ tailWord_4239873) baseStart_4239873 baseEnd_4239873 := by
    simpa [prefixWord, tailWord_4239873, baseEnd_4239873] using wordTrace_append hprefix tailTrace_4239873
  have hstable : (prefixWord ++ tailWord_4239873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4239873).length < 2 ^ (prefixWord ++ tailWord_4239873).sum := by decide
  have hdescent : baseEnd_4239873 < baseStart_4239873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4239873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4239899 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 4, 9]
def baseStart_4239899 : Nat := 118140960795 + 4239899 * 2 ^ 59
def prefixEnd_4239899 : Nat := 4983230072969 + 3 ^ 40 * 4239899 * 2
def baseEnd_4239899 : Nat := 725702037839137369787855

theorem tailTrace_4239899 : CollatzResearch.WordTrace tailWord_4239899 prefixEnd_4239899 725702037839137369787855 := by
  unfold tailWord_4239899
  simp only [CollatzResearch.WordTrace]
  refine ⟨154641820866577514944402751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103094547244385009962935167 154641820866577514944402751)
  ·
    refine ⟨231962731299866272416604127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154641820866577514944402751 231962731299866272416604127)
    ·
      refine ⟨347944096949799408624906191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231962731299866272416604127 347944096949799408624906191)
      ·
        refine ⟨521916145424699112937359287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 347944096949799408624906191 521916145424699112937359287)
        ·
          refine ⟨782874218137048669406038931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 521916145424699112937359287 782874218137048669406038931)
          ·
            refine ⟨1174311327205573004109058397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 782874218137048669406038931 1174311327205573004109058397)
            ·
              refine ⟨440366747702089876540896899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1174311327205573004109058397 440366747702089876540896899)
              ·
                refine ⟨660550121553134814811345349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 440366747702089876540896899 660550121553134814811345349)
                ·
                  refine ⟨123853147791212777777127253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 660550121553134814811345349 123853147791212777777127253)
                  ·
                    refine ⟨725702037839137369787855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 123853147791212777777127253 725702037839137369787855)
                    ·
                      rfl

theorem cell23_4239899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 9].length) (baseStart_4239899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4239899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4239899 prefixEnd_4239899 := by exact prefixLift 4239899
  have htrace : WordTrace (prefixWord ++ tailWord_4239899) baseStart_4239899 baseEnd_4239899 := by
    simpa [prefixWord, tailWord_4239899, baseEnd_4239899] using wordTrace_append hprefix tailTrace_4239899
  have hstable : (prefixWord ++ tailWord_4239899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4239899).length < 2 ^ (prefixWord ++ tailWord_4239899).sum := by decide
  have hdescent : baseEnd_4239899 < baseStart_4239899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4239899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4239907 : List Nat := [1, 1, 1, 4, 4, 3, 1, 3, 1, 4]
def baseStart_4239907 : Nat := 118140960795 + 4239907 * 2 ^ 59
def prefixEnd_4239907 : Nat := 4983230072969 + 3 ^ 40 * 4239907 * 2
def baseEnd_4239907 : Nat := 725703407120882692687843

theorem tailTrace_4239907 : CollatzResearch.WordTrace tailWord_4239907 prefixEnd_4239907 725703407120882692687843 := by
  unfold tailWord_4239907
  simp only [CollatzResearch.WordTrace]
  refine ⟨154642112650548532310693975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103094741767032354873795983 154642112650548532310693975)
  ·
    refine ⟨231963168975822798466040963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154642112650548532310693975 231963168975822798466040963)
    ·
      refine ⟨347944753463734197699061445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231963168975822798466040963 347944753463734197699061445)
      ·
        refine ⟨65239641274450162068574021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 347944753463734197699061445 65239641274450162068574021)
        ·
          refine ⟨12232432738959405387857629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65239641274450162068574021 12232432738959405387857629)
          ·
            refine ⟨4587162277109777020446611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12232432738959405387857629 4587162277109777020446611)
            ·
              refine ⟨6880743415664665530669917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4587162277109777020446611 6880743415664665530669917)
              ·
                refine ⟨2580278780874249574001219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6880743415664665530669917 2580278780874249574001219)
                ·
                  refine ⟨3870418171311374361001829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2580278780874249574001219 3870418171311374361001829)
                  ·
                    refine ⟨725703407120882692687843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3870418171311374361001829 725703407120882692687843)
                    ·
                      rfl

theorem cell23_4239907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 3, 1, 4].length) (baseStart_4239907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4239907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4239907 prefixEnd_4239907 := by exact prefixLift 4239907
  have htrace : WordTrace (prefixWord ++ tailWord_4239907) baseStart_4239907 baseEnd_4239907 := by
    simpa [prefixWord, tailWord_4239907, baseEnd_4239907] using wordTrace_append hprefix tailTrace_4239907
  have hstable : (prefixWord ++ tailWord_4239907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4239907).length < 2 ^ (prefixWord ++ tailWord_4239907).sum := by decide
  have hdescent : baseEnd_4239907 < baseStart_4239907 := by decide
  rcases family_descends (prefixWord ++ tailWord_4239907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4239924 : List Nat := [2, 5, 1, 3, 1, 2, 1, 1, 3, 4]
def baseStart_4239924 : Nat := 118140960795 + 4239924 * 2 ^ 59
def prefixEnd_4239924 : Nat := 4983230072969 + 3 ^ 40 * 4239924 * 2
def baseEnd_4239924 : Nat := 725706316844591503850317

theorem tailTrace_4239924 : CollatzResearch.WordTrace tailWord_4239924 prefixEnd_4239924 725706316844591503850317 := by
  unfold tailWord_4239924
  simp only [CollatzResearch.WordTrace]
  refine ⟨77321366345743472107031413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103095155127657962809375217 77321366345743472107031413)
  ·
    refine ⟨7248878094913450510034195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77321366345743472107031413 7248878094913450510034195)
    ·
      refine ⟨10873317142370175765051293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7248878094913450510034195 10873317142370175765051293)
      ·
        refine ⟨4077493928388815911894235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10873317142370175765051293 4077493928388815911894235)
        ·
          refine ⟨6116240892583223867841353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4077493928388815911894235 6116240892583223867841353)
          ·
            refine ⟨4587180669437417900881015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6116240892583223867841353 4587180669437417900881015)
            ·
              refine ⟨6880771004156126851321523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4587180669437417900881015 6880771004156126851321523)
              ·
                refine ⟨10321156506234190276982285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6880771004156126851321523 10321156506234190276982285)
                ·
                  refine ⟨3870433689837821353868357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10321156506234190276982285 3870433689837821353868357)
                  ·
                    refine ⟨725706316844591503850317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3870433689837821353868357 725706316844591503850317)
                    ·
                      rfl

theorem cell23_4239924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_4239924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4239924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4239924 prefixEnd_4239924 := by exact prefixLift 4239924
  have htrace : WordTrace (prefixWord ++ tailWord_4239924) baseStart_4239924 baseEnd_4239924 := by
    simpa [prefixWord, tailWord_4239924, baseEnd_4239924] using wordTrace_append hprefix tailTrace_4239924
  have hstable : (prefixWord ++ tailWord_4239924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4239924).length < 2 ^ (prefixWord ++ tailWord_4239924).sum := by decide
  have hdescent : baseEnd_4239924 < baseStart_4239924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4239924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4239930 : List Nat := [3, 1, 1, 1, 3, 3, 3, 1, 3, 1, 3]
def baseStart_4239930 : Nat := 118140960795 + 4239930 * 2 ^ 59
def prefixEnd_4239930 : Nat := 4983230072969 + 3 ^ 40 * 4239930 * 2
def baseEnd_4239930 : Nat := 2177122031417701488075923

theorem tailTrace_4239930 : CollatzResearch.WordTrace tailWord_4239930 prefixEnd_4239930 2177122031417701488075923 := by
  unfold tailWord_4239930
  simp only [CollatzResearch.WordTrace]
  refine ⟨38660737882366301809695311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103095301019643471492520829 38660737882366301809695311)
  ·
    refine ⟨57991106823549452714542967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38660737882366301809695311 57991106823549452714542967)
    ·
      refine ⟨86986660235324179071814451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57991106823549452714542967 86986660235324179071814451)
      ·
        refine ⟨130479990352986268607721677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86986660235324179071814451 130479990352986268607721677)
        ·
          refine ⟨48929996382369850727895629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130479990352986268607721677 48929996382369850727895629)
          ·
            refine ⟨18348748643388694022960861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48929996382369850727895629 18348748643388694022960861)
            ·
              refine ⟨6880780741270760258610323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18348748643388694022960861 6880780741270760258610323)
              ·
                refine ⟨10321171111906140387915485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6880780741270760258610323 10321171111906140387915485)
                ·
                  refine ⟨3870439166964802645468307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10321171111906140387915485 3870439166964802645468307)
                  ·
                    refine ⟨5805658750447203968202461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3870439166964802645468307 5805658750447203968202461)
                    ·
                      refine ⟨2177122031417701488075923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5805658750447203968202461 2177122031417701488075923)
                      ·
                        rfl

theorem cell23_4239930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 3, 1, 3].length) (baseStart_4239930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4239930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4239930 prefixEnd_4239930 := by exact prefixLift 4239930
  have htrace : WordTrace (prefixWord ++ tailWord_4239930) baseStart_4239930 baseEnd_4239930 := by
    simpa [prefixWord, tailWord_4239930, baseEnd_4239930] using wordTrace_append hprefix tailTrace_4239930
  have hstable : (prefixWord ++ tailWord_4239930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4239930).length < 2 ^ (prefixWord ++ tailWord_4239930).sum := by decide
  have hdescent : baseEnd_4239930 < baseStart_4239930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4239930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4239953 : List Nat := [1, 2, 2, 1, 3, 4, 1, 1, 3, 1, 4]
def baseStart_4239953 : Nat := 118140960795 + 4239953 * 2 ^ 59
def prefixEnd_4239953 : Nat := 4983230072969 + 3 ^ 40 * 4239953 * 2
def baseEnd_4239953 : Nat := 2177133841472754898088317

theorem tailTrace_4239953 : CollatzResearch.WordTrace tailWord_4239953 prefixEnd_4239953 2177133841472754898088317 := by
  unfold tailWord_4239953
  simp only [CollatzResearch.WordTrace]
  refine ⟨154643790408381882166868513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103095860272254588111245675 154643790408381882166868513)
  ·
    refine ⟨115982842806286411625151385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154643790408381882166868513 115982842806286411625151385)
    ·
      refine ⟨86987132104714808718863539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115982842806286411625151385 86987132104714808718863539)
      ·
        refine ⟨130480698157072213078295309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86987132104714808718863539 130480698157072213078295309)
        ·
          refine ⟨48930261808902079904360741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130480698157072213078295309 48930261808902079904360741)
          ·
            refine ⟨9174424089169139982067639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48930261808902079904360741 9174424089169139982067639)
            ·
              refine ⟨13761636133753709973101459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9174424089169139982067639 13761636133753709973101459)
              ·
                refine ⟨20642454200630564959652189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13761636133753709973101459 20642454200630564959652189)
                ·
                  refine ⟨7740920325236461859869571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20642454200630564959652189 7740920325236461859869571)
                  ·
                    refine ⟨11611380487854692789804357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7740920325236461859869571 11611380487854692789804357)
                    ·
                      refine ⟨2177133841472754898088317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11611380487854692789804357 2177133841472754898088317)
                      ·
                        rfl

theorem cell23_4239953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 3, 1, 4].length) (baseStart_4239953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4239953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4239953 prefixEnd_4239953 := by exact prefixLift 4239953
  have htrace : WordTrace (prefixWord ++ tailWord_4239953) baseStart_4239953 baseEnd_4239953 := by
    simpa [prefixWord, tailWord_4239953, baseEnd_4239953] using wordTrace_append hprefix tailTrace_4239953
  have hstable : (prefixWord ++ tailWord_4239953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4239953).length < 2 ^ (prefixWord ++ tailWord_4239953).sum := by decide
  have hdescent : baseEnd_4239953 < baseStart_4239953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4239953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4239976 : List Nat := [2, 1, 4, 3, 13]
def baseStart_4239976 : Nat := 118140960795 + 4239976 * 2 ^ 59
def prefixEnd_4239976 : Nat := 4983230072969 + 3 ^ 40 * 4239976 * 2
def baseEnd_4239976 : Nat := 2986482375209613591359

theorem tailTrace_4239976 : CollatzResearch.WordTrace tailWord_4239976 prefixEnd_4239976 2986482375209613591359 := by
  unfold tailWord_4239976
  simp only [CollatzResearch.WordTrace]
  refine ⟨77322314643649278547477891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103096419524865704729970521 77322314643649278547477891)
  ·
    refine ⟨115983471965473917821216837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77322314643649278547477891 115983471965473917821216837)
    ·
      refine ⟨21746900993526359591478157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115983471965473917821216837 21746900993526359591478157)
      ·
        refine ⟨8155087872572384846804309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21746900993526359591478157 8155087872572384846804309)
        ·
          refine ⟨2986482375209613591359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 8155087872572384846804309 2986482375209613591359)
          ·
            rfl

theorem cell23_4239976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 13].length) (baseStart_4239976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4239976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4239976 prefixEnd_4239976 := by exact prefixLift 4239976
  have htrace : WordTrace (prefixWord ++ tailWord_4239976) baseStart_4239976 baseEnd_4239976 := by
    simpa [prefixWord, tailWord_4239976, baseEnd_4239976] using wordTrace_append hprefix tailTrace_4239976
  have hstable : (prefixWord ++ tailWord_4239976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4239976).length < 2 ^ (prefixWord ++ tailWord_4239976).sum := by decide
  have hdescent : baseEnd_4239976 < baseStart_4239976 := by decide
  rcases family_descends (prefixWord ++ tailWord_4239976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4239981 : List Nat := [1, 5, 1, 1, 3, 3, 2, 2, 1, 1, 3]
def baseStart_4239981 : Nat := 118140960795 + 4239981 * 2 ^ 59
def prefixEnd_4239981 : Nat := 4983230072969 + 3 ^ 40 * 4239981 * 2
def baseEnd_4239981 : Nat := 2177148218931080788538189

theorem tailTrace_4239981 : CollatzResearch.WordTrace tailWord_4239981 prefixEnd_4239981 2177148218931080788538189 := by
  unfold tailWord_4239981
  simp only [CollatzResearch.WordTrace]
  refine ⟨154644811652280442948887797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103096541101520295299258531 154644811652280442948887797)
  ·
    refine ⟨14497951092401291526458231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 154644811652280442948887797 14497951092401291526458231)
    ·
      refine ⟨21746926638601937289687347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14497951092401291526458231 21746926638601937289687347)
      ·
        refine ⟨32620389957902905934531021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21746926638601937289687347 32620389957902905934531021)
        ·
          refine ⟨12232646234213589725449133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32620389957902905934531021 12232646234213589725449133)
          ·
            refine ⟨4587242337830096147043425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12232646234213589725449133 4587242337830096147043425)
            ·
              refine ⟨3440431753372572110282569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4587242337830096147043425 3440431753372572110282569)
              ·
                refine ⟨2580323815029429082711927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3440431753372572110282569 2580323815029429082711927)
                ·
                  refine ⟨3870485722544143624067891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2580323815029429082711927 3870485722544143624067891)
                  ·
                    refine ⟨5805728583816215436101837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3870485722544143624067891 5805728583816215436101837)
                    ·
                      refine ⟨2177148218931080788538189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5805728583816215436101837 2177148218931080788538189)
                      ·
                        rfl

theorem cell23_4239981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 2, 1, 1, 3].length) (baseStart_4239981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4239981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4239981 prefixEnd_4239981 := by exact prefixLift 4239981
  have htrace : WordTrace (prefixWord ++ tailWord_4239981) baseStart_4239981 baseEnd_4239981 := by
    simpa [prefixWord, tailWord_4239981, baseEnd_4239981] using wordTrace_append hprefix tailTrace_4239981
  have hstable : (prefixWord ++ tailWord_4239981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4239981).length < 2 ^ (prefixWord ++ tailWord_4239981).sum := by decide
  have hdescent : baseEnd_4239981 < baseStart_4239981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4239981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4239993 : List Nat := [1, 2, 1, 3, 3, 4, 1, 8]
def baseStart_4239993 : Nat := 118140960795 + 4239993 * 2 ^ 59
def prefixEnd_4239993 : Nat := 4983230072969 + 3 ^ 40 * 4239993 * 2
def baseEnd_4239993 : Nat := 80635347433293879318079

theorem tailTrace_4239993 : CollatzResearch.WordTrace tailWord_4239993 prefixEnd_4239993 80635347433293879318079 := by
  unfold tailWord_4239993
  simp only [CollatzResearch.WordTrace]
  refine ⟨154645249328236968998324633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103096832885491312665549755 154645249328236968998324633)
  ·
    refine ⟨115983936996177726748743475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154645249328236968998324633 115983936996177726748743475)
    ·
      refine ⟨173975905494266590123115213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115983936996177726748743475 173975905494266590123115213)
      ·
        refine ⟨65240964560349971296168205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 173975905494266590123115213 65240964560349971296168205)
        ·
          refine ⟨24465361710131239236063077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65240964560349971296168205 24465361710131239236063077)
          ·
            refine ⟨4587255320649607356761827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24465361710131239236063077 4587255320649607356761827)
            ·
              refine ⟨6880882980974411035142741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4587255320649607356761827 6880882980974411035142741)
              ·
                refine ⟨80635347433293879318079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6880882980974411035142741 80635347433293879318079)
                ·
                  rfl

theorem cell23_4239993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 8].length) (baseStart_4239993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4239993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4239993 prefixEnd_4239993 := by exact prefixLift 4239993
  have htrace : WordTrace (prefixWord ++ tailWord_4239993) baseStart_4239993 baseEnd_4239993 := by
    simpa [prefixWord, tailWord_4239993, baseEnd_4239993] using wordTrace_append hprefix tailTrace_4239993
  have hstable : (prefixWord ++ tailWord_4239993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4239993).length < 2 ^ (prefixWord ++ tailWord_4239993).sum := by decide
  have hdescent : baseEnd_4239993 < baseStart_4239993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4239993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4239996 : List Nat := [2, 2, 2, 1, 1, 2, 2, 1, 2, 2, 6]
def baseStart_4239996 : Nat := 118140960795 + 4239996 * 2 ^ 59
def prefixEnd_4239996 : Nat := 4983230072969 + 3 ^ 40 * 4239996 * 2
def baseEnd_4239996 : Nat := 2177155921140898229850619

theorem tailTrace_4239996 : CollatzResearch.WordTrace tailWord_4239996 prefixEnd_4239996 2177155921140898229850619 := by
  unfold tailWord_4239996
  simp only [CollatzResearch.WordTrace]
  refine ⟨77322679373613050255341921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103096905831484067007122561 77322679373613050255341921)
  ·
    refine ⟨57992009530209787691506441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77322679373613050255341921 57992009530209787691506441)
    ·
      refine ⟨43494007147657340768629831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57992009530209787691506441 43494007147657340768629831)
      ·
        refine ⟨65241010721486011152944747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43494007147657340768629831 65241010721486011152944747)
        ·
          refine ⟨97861516082229016729417121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65241010721486011152944747 97861516082229016729417121)
          ·
            refine ⟨73396137061671762547062841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97861516082229016729417121 73396137061671762547062841)
            ·
              refine ⟨55047102796253821910297131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73396137061671762547062841 55047102796253821910297131)
              ·
                refine ⟨82570654194380732865445697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55047102796253821910297131 82570654194380732865445697)
                ·
                  refine ⟨61927990645785549649084273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82570654194380732865445697 61927990645785549649084273)
                  ·
                    refine ⟨46445992984339162236813205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61927990645785549649084273 46445992984339162236813205)
                    ·
                      refine ⟨2177155921140898229850619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46445992984339162236813205 2177155921140898229850619)
                      ·
                        rfl

theorem cell23_4239996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_4239996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4239996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4239996 prefixEnd_4239996 := by exact prefixLift 4239996
  have htrace : WordTrace (prefixWord ++ tailWord_4239996) baseStart_4239996 baseEnd_4239996 := by
    simpa [prefixWord, tailWord_4239996, baseEnd_4239996] using wordTrace_append hprefix tailTrace_4239996
  have hstable : (prefixWord ++ tailWord_4239996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4239996).length < 2 ^ (prefixWord ++ tailWord_4239996).sum := by decide
  have hdescent : baseEnd_4239996 < baseStart_4239996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4239996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4240003 : List Nat := [1, 1, 1, 3, 3, 1, 3, 3, 1, 3, 3]
def baseStart_4240003 : Nat := 118140960795 + 4240003 * 2 ^ 59
def prefixEnd_4240003 : Nat := 4983230072969 + 3 ^ 40 * 4240003 * 2
def baseEnd_4240003 : Nat := 2177159515505479702463087

theorem tailTrace_4240003 : CollatzResearch.WordTrace tailWord_4240003 prefixEnd_4240003 2177159515505479702463087 := by
  unfold tailWord_4240003
  simp only [CollatzResearch.WordTrace]
  refine ⟨154645614058200740706188663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103097076038800493804125775 154645614058200740706188663)
  ·
    refine ⟨231968421087301111059282995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154645614058200740706188663 231968421087301111059282995)
    ·
      refine ⟨347952631630951666588924493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231968421087301111059282995 347952631630951666588924493)
      ·
        refine ⟨130482236861606874970846685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 347952631630951666588924493 130482236861606874970846685)
        ·
          refine ⟨48930838823102578114067507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130482236861606874970846685 48930838823102578114067507)
          ·
            refine ⟨73396258234653867171101261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48930838823102578114067507 73396258234653867171101261)
            ·
              refine ⟨27523596837995200189162973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73396258234653867171101261 27523596837995200189162973)
              ·
                refine ⟨10321348814248200070936115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27523596837995200189162973 10321348814248200070936115)
                ·
                  refine ⟨15482023221372300106404173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10321348814248200070936115 15482023221372300106404173)
                  ·
                    refine ⟨5805758708014612539901565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15482023221372300106404173 5805758708014612539901565)
                    ·
                      refine ⟨2177159515505479702463087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5805758708014612539901565 2177159515505479702463087)
                      ·
                        rfl

theorem cell23_4240003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 3, 3].length) (baseStart_4240003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4240003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4240003 prefixEnd_4240003 := by exact prefixLift 4240003
  have htrace : WordTrace (prefixWord ++ tailWord_4240003) baseStart_4240003 baseEnd_4240003 := by
    simpa [prefixWord, tailWord_4240003, baseEnd_4240003] using wordTrace_append hprefix tailTrace_4240003
  have hstable : (prefixWord ++ tailWord_4240003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4240003).length < 2 ^ (prefixWord ++ tailWord_4240003).sum := by decide
  have hdescent : baseEnd_4240003 < baseStart_4240003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4240003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4240010 : List Nat := [3, 1, 2, 3, 3, 1, 3, 7]
def baseStart_4240010 : Nat := 118140960795 + 4240010 * 2 ^ 59
def prefixEnd_4240010 : Nat := 4983230072969 + 3 ^ 40 * 4240010 * 2
def baseEnd_4240010 : Nat := 80635670735928191669465

theorem tailTrace_4240010 : CollatzResearch.WordTrace tailWord_4240010 prefixEnd_4240010 80635670735928191669465 := by
  unfold tailWord_4240010
  simp only [CollatzResearch.WordTrace]
  refine ⟨38661467342293845225423371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103097246246116920601128989 38661467342293845225423371)
  ·
    refine ⟨57992201013440767838135057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38661467342293845225423371 57992201013440767838135057)
    ·
      refine ⟨43494150760080575878601293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57992201013440767838135057 43494150760080575878601293)
      ·
        refine ⟨16310306535030215954475485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43494150760080575878601293 16310306535030215954475485)
        ·
          refine ⟨6116364950636330982928307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16310306535030215954475485 6116364950636330982928307)
          ·
            refine ⟨9174547425954496474392461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6116364950636330982928307 9174547425954496474392461)
            ·
              refine ⟨3440455284732936177897173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9174547425954496474392461 3440455284732936177897173)
              ·
                refine ⟨80635670735928191669465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3440455284732936177897173 80635670735928191669465)
                ·
                  rfl

theorem cell23_4240010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 7].length) (baseStart_4240010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4240010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4240010 prefixEnd_4240010 := by exact prefixLift 4240010
  have htrace : WordTrace (prefixWord ++ tailWord_4240010) baseStart_4240010 baseEnd_4240010 := by
    simpa [prefixWord, tailWord_4240010, baseEnd_4240010] using wordTrace_append hprefix tailTrace_4240010
  have hstable : (prefixWord ++ tailWord_4240010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4240010).length < 2 ^ (prefixWord ++ tailWord_4240010).sum := by decide
  have hdescent : baseEnd_4240010 < baseStart_4240010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4240010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4240100 : List Nat := [2, 3, 1, 1, 1, 6, 1, 1, 7]
def baseStart_4240100 : Nat := 118140960795 + 4240100 * 2 ^ 59
def prefixEnd_4240100 : Nat := 4983230072969 + 3 ^ 40 * 4240100 * 2
def baseEnd_4240100 : Nat := 241912147014329535883349

theorem tailTrace_4240100 : CollatzResearch.WordTrace tailWord_4240100 prefixEnd_4240100 241912147014329535883349 := by
  unfold tailWord_4240100
  simp only [CollatzResearch.WordTrace]
  refine ⟨77324575969424663136234877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103099434625899550848313169 77324575969424663136234877)
  ·
    refine ⟨28996715988534248676088079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77324575969424663136234877 28996715988534248676088079)
    ·
      refine ⟨43495073982801373014132119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28996715988534248676088079 43495073982801373014132119)
      ·
        refine ⟨65242610974202059521198179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43495073982801373014132119 65242610974202059521198179)
        ·
          refine ⟨97863916461303089281797269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65242610974202059521198179 97863916461303089281797269)
          ·
            refine ⟨4587371084123582310084247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 97863916461303089281797269 4587371084123582310084247)
            ·
              refine ⟨6881056626185373465126371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4587371084123582310084247 6881056626185373465126371)
              ·
                refine ⟨10321584939278060197689557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6881056626185373465126371 10321584939278060197689557)
                ·
                  refine ⟨241912147014329535883349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10321584939278060197689557 241912147014329535883349)
                  ·
                    rfl

theorem cell23_4240100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 7].length) (baseStart_4240100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4240100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4240100 prefixEnd_4240100 := by exact prefixLift 4240100
  have htrace : WordTrace (prefixWord ++ tailWord_4240100) baseStart_4240100 baseEnd_4240100 := by
    simpa [prefixWord, tailWord_4240100, baseEnd_4240100] using wordTrace_append hprefix tailTrace_4240100
  have hstable : (prefixWord ++ tailWord_4240100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4240100).length < 2 ^ (prefixWord ++ tailWord_4240100).sum := by decide
  have hdescent : baseEnd_4240100 < baseStart_4240100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4240100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4240111 : List Nat := [1, 1, 2, 1, 5, 4, 2, 1, 2, 2, 2]
def baseStart_4240111 : Nat := 118140960795 + 4240111 * 2 ^ 59
def prefixEnd_4240111 : Nat := 4983230072969 + 3 ^ 40 * 4240111 * 2
def baseEnd_4240111 : Nat := 2177214971416165279912591

theorem tailTrace_4240111 : CollatzResearch.WordTrace tailWord_4240111 prefixEnd_4240111 2177214971416165279912591 := by
  unfold tailWord_4240111
  simp only [CollatzResearch.WordTrace]
  refine ⟨154649553141809475151120187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103099702094539650100746791 154649553141809475151120187)
  ·
    refine ⟨231974329712714212726680281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154649553141809475151120187 231974329712714212726680281)
    ·
      refine ⟨173980747284535659545010211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231974329712714212726680281 173980747284535659545010211)
      ·
        refine ⟨260971120926803489317515317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173980747284535659545010211 260971120926803489317515317)
        ·
          refine ⟨24466042586887827123517061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 260971120926803489317515317 24466042586887827123517061)
          ·
            refine ⟨4587382985041467585659449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24466042586887827123517061 4587382985041467585659449)
            ·
              refine ⟨3440537238781100689244587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4587382985041467585659449 3440537238781100689244587)
              ·
                refine ⟨5160805858171651033866881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3440537238781100689244587 5160805858171651033866881)
                ·
                  refine ⟨3870604393628738275400161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5160805858171651033866881 3870604393628738275400161)
                  ·
                    refine ⟨2902953295221553706550121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3870604393628738275400161 2902953295221553706550121)
                    ·
                      refine ⟨2177214971416165279912591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2902953295221553706550121 2177214971416165279912591)
                      ·
                        rfl

theorem cell23_4240111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 1, 2, 2, 2].length) (baseStart_4240111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4240111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4240111 prefixEnd_4240111 := by exact prefixLift 4240111
  have htrace : WordTrace (prefixWord ++ tailWord_4240111) baseStart_4240111 baseEnd_4240111 := by
    simpa [prefixWord, tailWord_4240111, baseEnd_4240111] using wordTrace_append hprefix tailTrace_4240111
  have hstable : (prefixWord ++ tailWord_4240111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4240111).length < 2 ^ (prefixWord ++ tailWord_4240111).sum := by decide
  have hdescent : baseEnd_4240111 < baseStart_4240111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4240111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4240113 : List Nat := [1, 2, 2, 2, 2, 2, 1, 2, 4, 5]
def baseStart_4240113 : Nat := 118140960795 + 4240113 * 2 ^ 59
def prefixEnd_4240113 : Nat := 4983230072969 + 3 ^ 40 * 4240113 * 2
def baseEnd_4240113 : Nat := 725738666125824757362527

theorem tailTrace_4240113 : CollatzResearch.WordTrace tailWord_4240113 prefixEnd_4240113 725738666125824757362527 := by
  unfold tailWord_4240113
  simp only [CollatzResearch.WordTrace]
  refine ⟨154649626087802229492692993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103099750725201486328461995 154649626087802229492692993)
  ·
    refine ⟨115987219565851672119519745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154649626087802229492692993 115987219565851672119519745)
    ·
      refine ⟨86990414674388754089639809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115987219565851672119519745 86990414674388754089639809)
      ·
        refine ⟨65242811005791565567229857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86990414674388754089639809 65242811005791565567229857)
        ·
          refine ⟨48932108254343674175422393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65242811005791565567229857 48932108254343674175422393)
          ·
            refine ⟨36699081190757755631566795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48932108254343674175422393 36699081190757755631566795)
            ·
              refine ⟨55048621786136633447350193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36699081190757755631566795 55048621786136633447350193)
              ·
                refine ⟨41286466339602475085512645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55048621786136633447350193 41286466339602475085512645)
                ·
                  refine ⟨7741212438675464078533621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41286466339602475085512645 7741212438675464078533621)
                  ·
                    refine ⟨725738666125824757362527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7741212438675464078533621 725738666125824757362527)
                    ·
                      rfl

theorem cell23_4240113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 4, 5].length) (baseStart_4240113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4240113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4240113 prefixEnd_4240113 := by exact prefixLift 4240113
  have htrace : WordTrace (prefixWord ++ tailWord_4240113) baseStart_4240113 baseEnd_4240113 := by
    simpa [prefixWord, tailWord_4240113, baseEnd_4240113] using wordTrace_append hprefix tailTrace_4240113
  have hstable : (prefixWord ++ tailWord_4240113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4240113).length < 2 ^ (prefixWord ++ tailWord_4240113).sum := by decide
  have hdescent : baseEnd_4240113 < baseStart_4240113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4240113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4240133 : List Nat := [1, 3, 1, 1, 2, 1, 1, 5, 1, 3, 4]
def baseStart_4240133 : Nat := 118140960795 + 4240133 * 2 ^ 59
def prefixEnd_4240133 : Nat := 4983230072969 + 3 ^ 40 * 4240133 * 2
def baseEnd_4240133 : Nat := 2177226267990564193837489

theorem tailTrace_4240133 : CollatzResearch.WordTrace tailWord_4240133 prefixEnd_4240133 2177226267990564193837489 := by
  unfold tailWord_4240133
  simp only [CollatzResearch.WordTrace]
  refine ⟨154650355547729772908421053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103100237031819848605614035 154650355547729772908421053)
  ·
    refine ⟨57993883330398664840657895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154650355547729772908421053 57993883330398664840657895)
    ·
      refine ⟨86990824995597997260986843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57993883330398664840657895 86990824995597997260986843)
      ·
        refine ⟨130486237493396995891480265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86990824995597997260986843 130486237493396995891480265)
        ·
          refine ⟨97864678120047746918610199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130486237493396995891480265 97864678120047746918610199)
          ·
            refine ⟨146797017180071620377915299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97864678120047746918610199 146797017180071620377915299)
            ·
              refine ⟨220195525770107430566872949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146797017180071620377915299 220195525770107430566872949)
              ·
                refine ⟨20643330540947571615644339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 220195525770107430566872949 20643330540947571615644339)
                ·
                  refine ⟨30964995811421357423466509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20643330540947571615644339 30964995811421357423466509)
                  ·
                    refine ⟨11611873429283009033799941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30964995811421357423466509 11611873429283009033799941)
                    ·
                      refine ⟨2177226267990564193837489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11611873429283009033799941 2177226267990564193837489)
                      ·
                        rfl

theorem cell23_4240133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 3, 4].length) (baseStart_4240133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4240133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4240133 prefixEnd_4240133 := by exact prefixLift 4240133
  have htrace : WordTrace (prefixWord ++ tailWord_4240133) baseStart_4240133 baseEnd_4240133 := by
    simpa [prefixWord, tailWord_4240133, baseEnd_4240133] using wordTrace_append hprefix tailTrace_4240133
  have hstable : (prefixWord ++ tailWord_4240133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4240133).length < 2 ^ (prefixWord ++ tailWord_4240133).sum := by decide
  have hdescent : baseEnd_4240133 < baseStart_4240133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4240133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4240151 : List Nat := [1, 1, 3, 4, 4, 1, 2, 2, 5]
def baseStart_4240151 : Nat := 118140960795 + 4240151 * 2 ^ 59
def prefixEnd_4240151 : Nat := 4983230072969 + 3 ^ 40 * 4240151 * 2
def baseEnd_4240151 : Nat := 241915056738038347045823

theorem tailTrace_4240151 : CollatzResearch.WordTrace tailWord_4240151 prefixEnd_4240151 241915056738038347045823 := by
  unfold tailWord_4240151
  simp only [CollatzResearch.WordTrace]
  refine ⟨154651012061664561982576307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103100674707776374655050871 154651012061664561982576307)
  ·
    refine ⟨231976518092496842973864461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154651012061664561982576307 231976518092496842973864461)
    ·
      refine ⟨86991194284686316115199173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 231976518092496842973864461 86991194284686316115199173)
      ·
        refine ⟨16310848928378684271599845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86991194284686316115199173 16310848928378684271599845)
        ·
          refine ⟨3058284174071003300924971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16310848928378684271599845 3058284174071003300924971)
          ·
            refine ⟨4587426261106504951387457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3058284174071003300924971 4587426261106504951387457)
            ·
              refine ⟨3440569695829878713540593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4587426261106504951387457 3440569695829878713540593)
              ·
                refine ⟨2580427271872409035155445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3440569695829878713540593 2580427271872409035155445)
                ·
                  refine ⟨241915056738038347045823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2580427271872409035155445 241915056738038347045823)
                  ·
                    rfl

theorem cell23_4240151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 2, 5].length) (baseStart_4240151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4240151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4240151 prefixEnd_4240151 := by exact prefixLift 4240151
  have htrace : WordTrace (prefixWord ++ tailWord_4240151) baseStart_4240151 baseEnd_4240151 := by
    simpa [prefixWord, tailWord_4240151, baseEnd_4240151] using wordTrace_append hprefix tailTrace_4240151
  have hstable : (prefixWord ++ tailWord_4240151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4240151).length < 2 ^ (prefixWord ++ tailWord_4240151).sum := by decide
  have hdescent : baseEnd_4240151 < baseStart_4240151 := by decide
  rcases family_descends (prefixWord ++ tailWord_4240151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4240163 : List Nat := [1, 1, 1, 4, 2, 1, 1, 2, 2, 4, 4]
def baseStart_4240163 : Nat := 118140960795 + 4240163 * 2 ^ 59
def prefixEnd_4240163 : Nat := 4983230072969 + 3 ^ 40 * 4240163 * 2
def baseEnd_4240163 : Nat := 2177241672410199076462351

theorem tailTrace_4240163 : CollatzResearch.WordTrace tailWord_4240163 prefixEnd_4240163 2177241672410199076462351 := by
  unfold tailWord_4240163
  simp only [CollatzResearch.WordTrace]
  refine ⟨154651449737621088032013143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103100966491747392021342095 154651449737621088032013143)
  ·
    refine ⟨231977174606431632048019715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154651449737621088032013143 231977174606431632048019715)
    ·
      refine ⟨347965761909647448072029573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231977174606431632048019715 347965761909647448072029573)
      ·
        refine ⟨65243580358058896513505545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 347965761909647448072029573 65243580358058896513505545)
        ·
          refine ⟨48932685268544172385129159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65243580358058896513505545 48932685268544172385129159)
          ·
            refine ⟨73399027902816258577693739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48932685268544172385129159 73399027902816258577693739)
            ·
              refine ⟨110098541854224387866540609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73399027902816258577693739 110098541854224387866540609)
              ·
                refine ⟨82573906390668290899905457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110098541854224387866540609 82573906390668290899905457)
                ·
                  refine ⟨61930429793001218174929093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82573906390668290899905457 61930429793001218174929093)
                  ·
                    refine ⟨11611955586187728407799205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61930429793001218174929093 11611955586187728407799205)
                    ·
                      refine ⟨2177241672410199076462351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11611955586187728407799205 2177241672410199076462351)
                      ·
                        rfl

theorem cell23_4240163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_4240163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4240163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4240163 prefixEnd_4240163 := by exact prefixLift 4240163
  have htrace : WordTrace (prefixWord ++ tailWord_4240163) baseStart_4240163 baseEnd_4240163 := by
    simpa [prefixWord, tailWord_4240163, baseEnd_4240163] using wordTrace_append hprefix tailTrace_4240163
  have hstable : (prefixWord ++ tailWord_4240163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4240163).length < 2 ^ (prefixWord ++ tailWord_4240163).sum := by decide
  have hdescent : baseEnd_4240163 < baseStart_4240163 := by decide
  rcases family_descends (prefixWord ++ tailWord_4240163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4240217 : List Nat := [1, 2, 1, 2, 2, 4, 1, 3, 3, 1, 3]
def baseStart_4240217 : Nat := 118140960795 + 4240217 * 2 ^ 59
def prefixEnd_4240217 : Nat := 4983230072969 + 3 ^ 40 * 4240217 * 2
def baseEnd_4240217 : Nat := 2177269400365541865187103

theorem tailTrace_4240217 : CollatzResearch.WordTrace tailWord_4240217 prefixEnd_4240217 2177269400365541865187103 := by
  unfold tailWord_4240217
  simp only [CollatzResearch.WordTrace]
  refine ⟨154653419279425455254478905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103102279519616970169652603 154653419279425455254478905)
  ·
    refine ⟨115990064459569091440859179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154653419279425455254478905 115990064459569091440859179)
    ·
      refine ⟨173985096689353637161288769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115990064459569091440859179 173985096689353637161288769)
      ·
        refine ⟨130488822517015227870966577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173985096689353637161288769 130488822517015227870966577)
        ·
          refine ⟨97866616887761420903224933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130488822517015227870966577 97866616887761420903224933)
          ·
            refine ⟨18349990666455266419354675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 97866616887761420903224933 18349990666455266419354675)
            ·
              refine ⟨27524985999682899629032013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18349990666455266419354675 27524985999682899629032013)
              ·
                refine ⟨10321869749881087360887005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27524985999682899629032013 10321869749881087360887005)
                ·
                  refine ⟨3870701156205407760332627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10321869749881087360887005 3870701156205407760332627)
                  ·
                    refine ⟨5806051734308111640498941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3870701156205407760332627 5806051734308111640498941)
                    ·
                      refine ⟨2177269400365541865187103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5806051734308111640498941 2177269400365541865187103)
                      ·
                        rfl

theorem cell23_4240217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 3, 1, 3].length) (baseStart_4240217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4240217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4240217 prefixEnd_4240217 := by exact prefixLift 4240217
  have htrace : WordTrace (prefixWord ++ tailWord_4240217) baseStart_4240217 baseEnd_4240217 := by
    simpa [prefixWord, tailWord_4240217, baseEnd_4240217] using wordTrace_append hprefix tailTrace_4240217
  have hstable : (prefixWord ++ tailWord_4240217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4240217).length < 2 ^ (prefixWord ++ tailWord_4240217).sum := by decide
  have hdescent : baseEnd_4240217 < baseStart_4240217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4240217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4240227 : List Nat := [1, 1, 1, 5, 3, 1, 1, 2, 1, 5, 2]
def baseStart_4240227 : Nat := 118140960795 + 4240227 * 2 ^ 59
def prefixEnd_4240227 : Nat := 4983230072969 + 3 ^ 40 * 4240227 * 2
def baseEnd_4240227 : Nat := 2177274535172086826062057

theorem tailTrace_4240227 : CollatzResearch.WordTrace tailWord_4240227 prefixEnd_4240227 2177274535172086826062057 := by
  unfold tailWord_4240227
  simp only [CollatzResearch.WordTrace]
  refine ⟨154653784009389226962342935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103102522672926151308228623 154653784009389226962342935)
  ·
    refine ⟨231980676014083840443514403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154653784009389226962342935 231980676014083840443514403)
    ·
      refine ⟨347971014021125760665271605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231980676014083840443514403 347971014021125760665271605)
      ·
        refine ⟨32622282564480540062369213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 347971014021125760665271605 32622282564480540062369213)
        ·
          refine ⟨12233355961680202523388455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32622282564480540062369213 12233355961680202523388455)
          ·
            refine ⟨18350033942520303785082683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12233355961680202523388455 18350033942520303785082683)
            ·
              refine ⟨27525050913780455677624025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18350033942520303785082683 27525050913780455677624025)
              ·
                refine ⟨20643788185335341758218019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27525050913780455677624025 20643788185335341758218019)
                ·
                  refine ⟨30965682278003012637327029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20643788185335341758218019 30965682278003012637327029)
                  ·
                    refine ⟨2903032713562782434749409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30965682278003012637327029 2903032713562782434749409)
                    ·
                      refine ⟨2177274535172086826062057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2903032713562782434749409 2177274535172086826062057)
                      ·
                        rfl

theorem cell23_4240227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 5, 2].length) (baseStart_4240227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4240227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4240227 prefixEnd_4240227 := by exact prefixLift 4240227
  have htrace : WordTrace (prefixWord ++ tailWord_4240227) baseStart_4240227 baseEnd_4240227 := by
    simpa [prefixWord, tailWord_4240227, baseEnd_4240227] using wordTrace_append hprefix tailTrace_4240227
  have hstable : (prefixWord ++ tailWord_4240227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4240227).length < 2 ^ (prefixWord ++ tailWord_4240227).sum := by decide
  have hdescent : baseEnd_4240227 < baseStart_4240227 := by decide
  rcases family_descends (prefixWord ++ tailWord_4240227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4240240 : List Nat := [2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 4]
def baseStart_4240240 : Nat := 118140960795 + 4240240 * 2 ^ 59
def prefixEnd_4240240 : Nat := 4983230072969 + 3 ^ 40 * 4240240 * 2
def baseEnd_4240240 : Nat := 2177281210420595275199497

theorem tailTrace_4240240 : CollatzResearch.WordTrace tailWord_4240240 prefixEnd_4240240 2177281210420595275199497 := by
  unfold tailWord_4240240
  simp only [CollatzResearch.WordTrace]
  refine ⟨77327129079171065091283087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103102838772228086788377449 77327129079171065091283087)
  ·
    refine ⟨115990693618756597636924631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77327129079171065091283087 115990693618756597636924631)
    ·
      refine ⟨173986040428134896455386947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115990693618756597636924631 173986040428134896455386947)
      ·
        refine ⟨260979060642202344683080421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173986040428134896455386947 260979060642202344683080421)
        ·
          refine ⟨48933573870412939628077579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 260979060642202344683080421 48933573870412939628077579)
          ·
            refine ⟨73400360805619409442116369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48933573870412939628077579 73400360805619409442116369)
            ·
              refine ⟨55050270604214557081587277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73400360805619409442116369 55050270604214557081587277)
              ·
                refine ⟨20643851476580458905595229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55050270604214557081587277 20643851476580458905595229)
                ·
                  refine ⟨7741444303717672089598211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20643851476580458905595229 7741444303717672089598211)
                  ·
                    refine ⟨11612166455576508134397317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7741444303717672089598211 11612166455576508134397317)
                    ·
                      refine ⟨2177281210420595275199497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11612166455576508134397317 2177281210420595275199497)
                      ·
                        rfl

theorem cell23_4240240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 4].length) (baseStart_4240240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4240240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4240240 prefixEnd_4240240 := by exact prefixLift 4240240
  have htrace : WordTrace (prefixWord ++ tailWord_4240240) baseStart_4240240 baseEnd_4240240 := by
    simpa [prefixWord, tailWord_4240240, baseEnd_4240240] using wordTrace_append hprefix tailTrace_4240240
  have hstable : (prefixWord ++ tailWord_4240240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4240240).length < 2 ^ (prefixWord ++ tailWord_4240240).sum := by decide
  have hdescent : baseEnd_4240240 < baseStart_4240240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4240240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4240307 : List Nat := [1, 1, 1, 2, 3, 1, 2, 4, 4, 1, 3]
def baseStart_4240307 : Nat := 118140960795 + 4240307 * 2 ^ 59
def prefixEnd_4240307 : Nat := 4983230072969 + 3 ^ 40 * 4240307 * 2
def baseEnd_4240307 : Nat := 2177315613624446513061689

theorem tailTrace_4240307 : CollatzResearch.WordTrace tailWord_4240307 prefixEnd_4240307 2177315613624446513061689 := by
  unfold tailWord_4240307
  simp only [CollatzResearch.WordTrace]
  refine ⟨154656701849099400625255175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103104467899399600416836783 154656701849099400625255175)
  ·
    refine ⟨231985052773649100937882763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154656701849099400625255175 231985052773649100937882763)
    ·
      refine ⟨347977579160473651406824145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231985052773649100937882763 347977579160473651406824145)
      ·
        refine ⟨260983184370355238555118109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 347977579160473651406824145 260983184370355238555118109)
        ·
          refine ⟨97868694138883214458169291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 260983184370355238555118109 97868694138883214458169291)
          ·
            refine ⟨146803041208324821687253937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97868694138883214458169291 146803041208324821687253937)
            ·
              refine ⟨110102280906243616265440453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146803041208324821687253937 110102280906243616265440453)
              ·
                refine ⟨20644177669920678049770085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 110102280906243616265440453 20644177669920678049770085)
                ·
                  refine ⟨3870783313110127134331891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20644177669920678049770085 3870783313110127134331891)
                  ·
                    refine ⟨5806174969665190701497837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3870783313110127134331891 5806174969665190701497837)
                    ·
                      refine ⟨2177315613624446513061689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5806174969665190701497837 2177315613624446513061689)
                      ·
                        rfl

theorem cell23_4240307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 4, 1, 3].length) (baseStart_4240307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4240307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4240307 prefixEnd_4240307 := by exact prefixLift 4240307
  have htrace : WordTrace (prefixWord ++ tailWord_4240307) baseStart_4240307 baseEnd_4240307 := by
    simpa [prefixWord, tailWord_4240307, baseEnd_4240307] using wordTrace_append hprefix tailTrace_4240307
  have hstable : (prefixWord ++ tailWord_4240307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4240307).length < 2 ^ (prefixWord ++ tailWord_4240307).sum := by decide
  have hdescent : baseEnd_4240307 < baseStart_4240307 := by decide
  rcases family_descends (prefixWord ++ tailWord_4240307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4240308 : List Nat := [2, 5, 2, 1, 1, 2, 3, 1, 1, 1, 4]
def baseStart_4240308 : Nat := 118140960795 + 4240308 * 2 ^ 59
def prefixEnd_4240308 : Nat := 4983230072969 + 3 ^ 40 * 4240308 * 2
def baseEnd_4240308 : Nat := 2177316127105101009149185

theorem tailTrace_4240308 : CollatzResearch.WordTrace tailWord_4240308 prefixEnd_4240308 2177316127105101009149185 := by
  unfold tailWord_4240308
  simp only [CollatzResearch.WordTrace]
  refine ⟨77328369161047888898020789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103104492214730518530694385 77328369161047888898020789)
  ·
    refine ⟨7249534608848239584189449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77328369161047888898020789 7249534608848239584189449)
    ·
      refine ⟨5437150956636179688142087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7249534608848239584189449 5437150956636179688142087)
      ·
        refine ⟨8155726434954269532213131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5437150956636179688142087 8155726434954269532213131)
        ·
          refine ⟨12233589652431404298319697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8155726434954269532213131 12233589652431404298319697)
          ·
            refine ⟨9175192239323553223739773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12233589652431404298319697 9175192239323553223739773)
            ·
              refine ⟨3440697089746332458902415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9175192239323553223739773 3440697089746332458902415)
              ·
                refine ⟨5161045634619498688353623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3440697089746332458902415 5161045634619498688353623)
                ·
                  refine ⟨7741568451929248032530435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5161045634619498688353623 7741568451929248032530435)
                  ·
                    refine ⟨11612352677893872048795653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7741568451929248032530435 11612352677893872048795653)
                    ·
                      refine ⟨2177316127105101009149185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11612352677893872048795653 2177316127105101009149185)
                      ·
                        rfl

theorem cell23_4240308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_4240308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4240308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4240308 prefixEnd_4240308 := by exact prefixLift 4240308
  have htrace : WordTrace (prefixWord ++ tailWord_4240308) baseStart_4240308 baseEnd_4240308 := by
    simpa [prefixWord, tailWord_4240308, baseEnd_4240308] using wordTrace_append hprefix tailTrace_4240308
  have hstable : (prefixWord ++ tailWord_4240308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4240308).length < 2 ^ (prefixWord ++ tailWord_4240308).sum := by decide
  have hdescent : baseEnd_4240308 < baseStart_4240308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4240308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4240334 : List Nat := [4, 1, 1, 1, 2, 3, 1, 2, 3, 3, 2]
def baseStart_4240334 : Nat := 118140960795 + 4240334 * 2 ^ 59
def prefixEnd_4240334 : Nat := 4983230072969 + 3 ^ 40 * 4240334 * 2
def baseEnd_4240334 : Nat := 2177329477602117907424065

theorem tailTrace_4240334 : CollatzResearch.WordTrace tailWord_4240334 prefixEnd_4240334 2177329477602117907424065 := by
  unfold tailWord_4240334
  simp only [CollatzResearch.WordTrace]
  refine ⟨19332210827500198029561007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103105124413334389490992037 19332210827500198029561007)
  ·
    refine ⟨28998316241250297044341511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19332210827500198029561007 28998316241250297044341511)
    ·
      refine ⟨43497474361875445566512267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28998316241250297044341511 43497474361875445566512267)
      ·
        refine ⟨65246211542813168349768401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43497474361875445566512267 65246211542813168349768401)
        ·
          refine ⟨48934658657109876262326301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65246211542813168349768401 48934658657109876262326301)
          ·
            refine ⟨18350496996416203598372363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48934658657109876262326301 18350496996416203598372363)
            ·
              refine ⟨27525745494624305397558545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18350496996416203598372363 27525745494624305397558545)
              ·
                refine ⟨20644309120968229048168909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27525745494624305397558545 20644309120968229048168909)
                ·
                  refine ⟨7741615920363085893063341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20644309120968229048168909 7741615920363085893063341)
                  ·
                    refine ⟨2903105970136157209898753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7741615920363085893063341 2903105970136157209898753)
                    ·
                      refine ⟨2177329477602117907424065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2903105970136157209898753 2177329477602117907424065)
                      ·
                        rfl

theorem cell23_4240334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 3, 3, 2].length) (baseStart_4240334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4240334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4240334 prefixEnd_4240334 := by exact prefixLift 4240334
  have htrace : WordTrace (prefixWord ++ tailWord_4240334) baseStart_4240334 baseEnd_4240334 := by
    simpa [prefixWord, tailWord_4240334, baseEnd_4240334] using wordTrace_append hprefix tailTrace_4240334
  have hstable : (prefixWord ++ tailWord_4240334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4240334).length < 2 ^ (prefixWord ++ tailWord_4240334).sum := by decide
  have hdescent : baseEnd_4240334 < baseStart_4240334 := by decide
  rcases family_descends (prefixWord ++ tailWord_4240334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4240402 : List Nat := [3, 2, 5, 1, 1, 1, 2, 2, 1, 3, 2]
def baseStart_4240402 : Nat := 118140960795 + 4240402 * 2 ^ 59
def prefixEnd_4240402 : Nat := 4983230072969 + 3 ^ 40 * 4240402 * 2
def baseEnd_4240402 : Nat := 2177364394286623641373753

theorem tailTrace_4240402 : CollatzResearch.WordTrace tailWord_4240402 prefixEnd_4240402 2177364394286623641373753 := by
  unfold tailWord_4240402
  simp only [CollatzResearch.WordTrace]
  refine ⟨38665041695938807962490865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103106777855836821233308973 38665041695938807962490865)
  ·
    refine ⟨28998781271954105971868149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38665041695938807962490865 28998781271954105971868149)
    ·
      refine ⟨2718635744245697434862639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28998781271954105971868149 2718635744245697434862639)
      ·
        refine ⟨4077953616368546152293959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2718635744245697434862639 4077953616368546152293959)
        ·
          refine ⟨6116930424552819228440939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4077953616368546152293959 6116930424552819228440939)
          ·
            refine ⟨9175395636829228842661409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6116930424552819228440939 9175395636829228842661409)
            ·
              refine ⟨6881546727621921631996057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9175395636829228842661409 6881546727621921631996057)
              ·
                refine ⟨5161160045716441223997043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6881546727621921631996057 5161160045716441223997043)
                ·
                  refine ⟨7741740068574661835995565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5161160045716441223997043 7741740068574661835995565)
                  ·
                    refine ⟨2903152525715498188498337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7741740068574661835995565 2903152525715498188498337)
                    ·
                      refine ⟨2177364394286623641373753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2903152525715498188498337 2177364394286623641373753)
                      ·
                        rfl

theorem cell23_4240402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_4240402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4240402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4240402 prefixEnd_4240402 := by exact prefixLift 4240402
  have htrace : WordTrace (prefixWord ++ tailWord_4240402) baseStart_4240402 baseEnd_4240402 := by
    simpa [prefixWord, tailWord_4240402, baseEnd_4240402] using wordTrace_append hprefix tailTrace_4240402
  have hstable : (prefixWord ++ tailWord_4240402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4240402).length < 2 ^ (prefixWord ++ tailWord_4240402).sum := by decide
  have hdescent : baseEnd_4240402 < baseStart_4240402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4240402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4240417 : List Nat := [1, 2, 3, 2, 3, 1, 2, 1, 1, 7]
def baseStart_4240417 : Nat := 118140960795 + 4240417 * 2 ^ 59
def prefixEnd_4240417 : Nat := 4983230072969 + 3 ^ 40 * 4240417 * 2
def baseEnd_4240417 : Nat := 725790698832147027562061

theorem tailTrace_4240417 : CollatzResearch.WordTrace tailWord_4240417 prefixEnd_4240417 725790698832147027562061 := by
  unfold tailWord_4240417
  simp only [CollatzResearch.WordTrace]
  refine ⟨154660713878700889411759505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103107142585800592941173003 154660713878700889411759505)
  ·
    refine ⟨115995535409025667058819629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154660713878700889411759505 115995535409025667058819629)
    ·
      refine ⟨43498325778384625147057361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115995535409025667058819629 43498325778384625147057361)
      ·
        refine ⟨32623744333788468860293021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43498325778384625147057361 32623744333788468860293021)
        ·
          refine ⟨12233904125170675822609883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32623744333788468860293021 12233904125170675822609883)
          ·
            refine ⟨18350856187756013733914825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12233904125170675822609883 18350856187756013733914825)
            ·
              refine ⟨13763142140817010300436119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18350856187756013733914825 13763142140817010300436119)
              ·
                refine ⟨20644713211225515450654179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13763142140817010300436119 20644713211225515450654179)
                ·
                  refine ⟨30967069816838273175981269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20644713211225515450654179 30967069816838273175981269)
                  ·
                    refine ⟨725790698832147027562061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30967069816838273175981269 725790698832147027562061)
                    ·
                      rfl

theorem cell23_4240417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 7].length) (baseStart_4240417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4240417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4240417 prefixEnd_4240417 := by exact prefixLift 4240417
  have htrace : WordTrace (prefixWord ++ tailWord_4240417) baseStart_4240417 baseEnd_4240417 := by
    simpa [prefixWord, tailWord_4240417, baseEnd_4240417] using wordTrace_append hprefix tailTrace_4240417
  have hstable : (prefixWord ++ tailWord_4240417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4240417).length < 2 ^ (prefixWord ++ tailWord_4240417).sum := by decide
  have hdescent : baseEnd_4240417 < baseStart_4240417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4240417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4240438 : List Nat := [5, 1, 2, 1, 1, 3, 3, 2, 5]
def baseStart_4240438 : Nat := 118140960795 + 4240438 * 2 ^ 59
def prefixEnd_4240438 : Nat := 4983230072969 + 3 ^ 40 * 4240438 * 2
def baseEnd_4240438 : Nat := 241931431065576166724843

theorem tailTrace_4240438 : CollatzResearch.WordTrace tailWord_4240438 prefixEnd_4240438 241931431065576166724843 := by
  unfold tailWord_4240438
  simp only [CollatzResearch.WordTrace]
  refine ⟨9666342488226550624892123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 103107653207749873332182645 9666342488226550624892123)
  ·
    refine ⟨14499513732339825937338185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9666342488226550624892123 14499513732339825937338185)
    ·
      refine ⟨10874635299254869453003639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14499513732339825937338185 10874635299254869453003639)
      ·
        refine ⟨16311952948882304179505459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10874635299254869453003639 16311952948882304179505459)
        ·
          refine ⟨24467929423323456269258189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16311952948882304179505459 24467929423323456269258189)
          ·
            refine ⟨9175473533746296100971821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24467929423323456269258189 9175473533746296100971821)
            ·
              refine ⟨3440802575154861037864433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9175473533746296100971821 3440802575154861037864433)
              ·
                refine ⟨2580601931366145778398325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3440802575154861037864433 2580601931366145778398325)
                ·
                  refine ⟨241931431065576166724843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2580601931366145778398325 241931431065576166724843)
                  ·
                    rfl

theorem cell23_4240438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 2, 5].length) (baseStart_4240438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4240438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4240438 prefixEnd_4240438 := by exact prefixLift 4240438
  have htrace : WordTrace (prefixWord ++ tailWord_4240438) baseStart_4240438 baseEnd_4240438 := by
    simpa [prefixWord, tailWord_4240438, baseEnd_4240438] using wordTrace_append hprefix tailTrace_4240438
  have hstable : (prefixWord ++ tailWord_4240438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4240438).length < 2 ^ (prefixWord ++ tailWord_4240438).sum := by decide
  have hdescent : baseEnd_4240438 < baseStart_4240438 := by decide
  rcases family_descends (prefixWord ++ tailWord_4240438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4240457 : List Nat := [1, 2, 1, 1, 2, 2, 2, 4, 1, 4, 3]
def baseStart_4240457 : Nat := 118140960795 + 4240457 * 2 ^ 59
def prefixEnd_4240457 : Nat := 4983230072969 + 3 ^ 40 * 4240457 * 2
def baseEnd_4240457 : Nat := 2177392635722620926185999

theorem tailTrace_4240457 : CollatzResearch.WordTrace tailWord_4240457 prefixEnd_4240457 2177392635722620926185999 := by
  unfold tailWord_4240457
  simp only [CollatzResearch.WordTrace]
  refine ⟨154662172798555976243215625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103108115199037317495477083 154662172798555976243215625)
  ·
    refine ⟨115996629598916982182411719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154662172798555976243215625 115996629598916982182411719)
    ·
      refine ⟨173994944398375473273617579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115996629598916982182411719 173994944398375473273617579)
      ·
        refine ⟨260992416597563209910426369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173994944398375473273617579 260992416597563209910426369)
        ·
          refine ⟨195744312448172407432819777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 260992416597563209910426369 195744312448172407432819777)
          ·
            refine ⟨146808234336129305574614833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 195744312448172407432819777 146808234336129305574614833)
            ·
              refine ⟨110106175752096979180961125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146808234336129305574614833 110106175752096979180961125)
              ·
                refine ⟨20644907953518183596430211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 110106175752096979180961125 20644907953518183596430211)
                ·
                  refine ⟨30967361930277275394645317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20644907953518183596430211 30967361930277275394645317)
                  ·
                    refine ⟨5806380361926989136495997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30967361930277275394645317 5806380361926989136495997)
                    ·
                      refine ⟨2177392635722620926185999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5806380361926989136495997 2177392635722620926185999)
                      ·
                        rfl

theorem cell23_4240457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 4, 3].length) (baseStart_4240457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4240457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4240457 prefixEnd_4240457 := by exact prefixLift 4240457
  have htrace : WordTrace (prefixWord ++ tailWord_4240457) baseStart_4240457 baseEnd_4240457 := by
    simpa [prefixWord, tailWord_4240457, baseEnd_4240457] using wordTrace_append hprefix tailTrace_4240457
  have hstable : (prefixWord ++ tailWord_4240457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4240457).length < 2 ^ (prefixWord ++ tailWord_4240457).sum := by decide
  have hdescent : baseEnd_4240457 < baseStart_4240457 := by decide
  rcases family_descends (prefixWord ++ tailWord_4240457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4240494 : List Nat := [4, 1, 2, 2, 1, 2, 1, 4, 6]
def baseStart_4240494 : Nat := 118140960795 + 4240494 * 2 ^ 59
def prefixEnd_4240494 : Nat := 4983230072969 + 3 ^ 40 * 4240494 * 2
def baseEnd_4240494 : Nat := 241934626056315253491481

theorem tailTrace_4240494 : CollatzResearch.WordTrace tailWord_4240494 prefixEnd_4240494 241934626056315253491481 := by
  unfold tailWord_4240494
  simp only [CollatzResearch.WordTrace]
  refine ⟨19332940287427741445289067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103109014866281287708208357 19332940287427741445289067)
  ·
    refine ⟨28999410431141612167933601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19332940287427741445289067 28999410431141612167933601)
    ·
      refine ⟨21749557823356209125950201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28999410431141612167933601 21749557823356209125950201)
      ·
        refine ⟨16312168367517156844462651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21749557823356209125950201 16312168367517156844462651)
        ·
          refine ⟨24468252551275735266693977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16312168367517156844462651 24468252551275735266693977)
          ·
            refine ⟨18351189413456801450020483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24468252551275735266693977 18351189413456801450020483)
            ·
              refine ⟨27526784120185202175030725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18351189413456801450020483 27526784120185202175030725)
              ·
                refine ⟨5161272022534725407818261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27526784120185202175030725 5161272022534725407818261)
                ·
                  refine ⟨241934626056315253491481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5161272022534725407818261 241934626056315253491481)
                  ·
                    rfl

theorem cell23_4240494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 4, 6].length) (baseStart_4240494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4240494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4240494 prefixEnd_4240494 := by exact prefixLift 4240494
  have htrace : WordTrace (prefixWord ++ tailWord_4240494) baseStart_4240494 baseEnd_4240494 := by
    simpa [prefixWord, tailWord_4240494, baseEnd_4240494] using wordTrace_append hprefix tailTrace_4240494
  have hstable : (prefixWord ++ tailWord_4240494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4240494).length < 2 ^ (prefixWord ++ tailWord_4240494).sum := by decide
  have hdescent : baseEnd_4240494 < baseStart_4240494 := by decide
  rcases family_descends (prefixWord ++ tailWord_4240494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4240521 : List Nat := [1, 2, 1, 1, 4, 4, 1, 2, 3, 1, 3]
def baseStart_4240521 : Nat := 118140960795 + 4240521 * 2 ^ 59
def prefixEnd_4240521 : Nat := 4983230072969 + 3 ^ 40 * 4240521 * 2
def baseEnd_4240521 : Nat := 2177425498484508675785705

theorem tailTrace_4240521 : CollatzResearch.WordTrace tailWord_4240521 prefixEnd_4240521 2177425498484508675785705 := by
  unfold tailWord_4240521
  simp only [CollatzResearch.WordTrace]
  refine ⟨154664507070324115173545417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103109671380216076782363611 154664507070324115173545417)
  ·
    refine ⟨115998380302743086380159063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154664507070324115173545417 115998380302743086380159063)
    ·
      refine ⟨173997570454114629570238595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115998380302743086380159063 173997570454114629570238595)
      ·
        refine ⟨260996355681171944355357893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173997570454114629570238595 260996355681171944355357893)
        ·
          refine ⟨48936816690219739566629605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 260996355681171944355357893 48936816690219739566629605)
          ·
            refine ⟨9175653129416201168743051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48936816690219739566629605 9175653129416201168743051)
            ·
              refine ⟨13763479694124301753114577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9175653129416201168743051 13763479694124301753114577)
              ·
                refine ⟨10322609770593226314835933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13763479694124301753114577 10322609770593226314835933)
                ·
                  refine ⟨3870978663972459868063475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10322609770593226314835933 3870978663972459868063475)
                  ·
                    refine ⟨5806467995958689802095213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3870978663972459868063475 5806467995958689802095213)
                    ·
                      refine ⟨2177425498484508675785705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5806467995958689802095213 2177425498484508675785705)
                      ·
                        rfl

theorem cell23_4240521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 3, 1, 3].length) (baseStart_4240521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4240521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4240521 prefixEnd_4240521 := by exact prefixLift 4240521
  have htrace : WordTrace (prefixWord ++ tailWord_4240521) baseStart_4240521 baseEnd_4240521 := by
    simpa [prefixWord, tailWord_4240521, baseEnd_4240521] using wordTrace_append hprefix tailTrace_4240521
  have hstable : (prefixWord ++ tailWord_4240521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4240521).length < 2 ^ (prefixWord ++ tailWord_4240521).sum := by decide
  have hdescent : baseEnd_4240521 < baseStart_4240521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4240521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4240531 : List Nat := [1, 1, 1, 2, 1, 2, 7, 1, 2, 3, 2]
def baseStart_4240531 : Nat := 118140960795 + 4240531 * 2 ^ 59
def prefixEnd_4240531 : Nat := 4983230072969 + 3 ^ 40 * 4240531 * 2
def baseEnd_4240531 : Nat := 2177430633291053636660659

theorem tailTrace_4240531 : CollatzResearch.WordTrace tailWord_4240531 prefixEnd_4240531 2177430633291053636660659 := by
  unfold tailWord_4240531
  simp only [CollatzResearch.WordTrace]
  refine ⟨154664871800287886881409447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103109914533525257920939631 154664871800287886881409447)
  ·
    refine ⟨231997307700431830322114171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154664871800287886881409447 231997307700431830322114171)
    ·
      refine ⟨347995961550647745483171257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231997307700431830322114171 347995961550647745483171257)
      ·
        refine ⟨260996971162985809112378443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 347995961550647745483171257 260996971162985809112378443)
        ·
          refine ⟨391495456744478713668567665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260996971162985809112378443 391495456744478713668567665)
          ·
            refine ⟨293621592558359035251425749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 391495456744478713668567665 293621592558359035251425749)
            ·
              refine ⟨6881756075586539888705291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 293621592558359035251425749 6881756075586539888705291)
              ·
                refine ⟨10322634113379809833057937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6881756075586539888705291 10322634113379809833057937)
                ·
                  refine ⟨7741975585034857374793453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10322634113379809833057937 7741975585034857374793453)
                  ·
                    refine ⟨2903240844388071515547545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7741975585034857374793453 2903240844388071515547545)
                    ·
                      refine ⟨2177430633291053636660659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2903240844388071515547545 2177430633291053636660659)
                      ·
                        rfl

theorem cell23_4240531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 2, 3, 2].length) (baseStart_4240531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4240531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4240531 prefixEnd_4240531 := by exact prefixLift 4240531
  have htrace : WordTrace (prefixWord ++ tailWord_4240531) baseStart_4240531 baseEnd_4240531 := by
    simpa [prefixWord, tailWord_4240531, baseEnd_4240531] using wordTrace_append hprefix tailTrace_4240531
  have hstable : (prefixWord ++ tailWord_4240531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4240531).length < 2 ^ (prefixWord ++ tailWord_4240531).sum := by decide
  have hdescent : baseEnd_4240531 < baseStart_4240531 := by decide
  rcases family_descends (prefixWord ++ tailWord_4240531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4240547 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 5]
def baseStart_4240547 : Nat := 118140960795 + 4240547 * 2 ^ 59
def prefixEnd_4240547 : Nat := 4983230072969 + 3 ^ 40 * 4240547 * 2
def baseEnd_4240547 : Nat := 2177438848981525574060585

theorem tailTrace_4240547 : CollatzResearch.WordTrace tailWord_4240547 prefixEnd_4240547 2177438848981525574060585 := by
  unfold tailWord_4240547
  simp only [CollatzResearch.WordTrace]
  refine ⟨154665455368229921613991895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103110303578819947742661263 154665455368229921613991895)
  ·
    refine ⟨231998183052344882420987843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154665455368229921613991895 231998183052344882420987843)
    ·
      refine ⟨347997274578517323631481765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231998183052344882420987843 347997274578517323631481765)
      ·
        refine ⟨65249488983471998180902831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 347997274578517323631481765 65249488983471998180902831)
        ·
          refine ⟨97874233475207997271354247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65249488983471998180902831 97874233475207997271354247)
          ·
            refine ⟨146811350212811995907031371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97874233475207997271354247 146811350212811995907031371)
            ·
              refine ⟨220217025319217993860547057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146811350212811995907031371 220217025319217993860547057)
              ·
                refine ⟨165162768989413495395410293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 220217025319217993860547057 165162768989413495395410293)
                ·
                  refine ⟨15484009592757515193319715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 165162768989413495395410293 15484009592757515193319715)
                  ·
                    refine ⟨23226014389136272789979573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15484009592757515193319715 23226014389136272789979573)
                    ·
                      refine ⟨2177438848981525574060585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23226014389136272789979573 2177438848981525574060585)
                      ·
                        rfl

theorem cell23_4240547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_4240547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4240547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4240547 prefixEnd_4240547 := by exact prefixLift 4240547
  have htrace : WordTrace (prefixWord ++ tailWord_4240547) baseStart_4240547 baseEnd_4240547 := by
    simpa [prefixWord, tailWord_4240547, baseEnd_4240547] using wordTrace_append hprefix tailTrace_4240547
  have hstable : (prefixWord ++ tailWord_4240547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4240547).length < 2 ^ (prefixWord ++ tailWord_4240547).sum := by decide
  have hdescent : baseEnd_4240547 < baseStart_4240547 := by decide
  rcases family_descends (prefixWord ++ tailWord_4240547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4240567 : List Nat := [1, 1, 3, 1, 4, 1, 2, 10]
def baseStart_4240567 : Nat := 118140960795 + 4240567 * 2 ^ 59
def prefixEnd_4240567 : Nat := 4983230072969 + 3 ^ 40 * 4240567 * 2
def baseEnd_4240567 : Nat := 80646263651652425770759

theorem tailTrace_4240567 : CollatzResearch.WordTrace tailWord_4240567 prefixEnd_4240567 80646263651652425770759 := by
  unfold tailWord_4240567
  simp only [CollatzResearch.WordTrace]
  refine ⟨154666184828157465029719955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103110789885438310019813303 154666184828157465029719955)
  ·
    refine ⟨231999277242236197544579933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154666184828157465029719955 231999277242236197544579933)
    ·
      refine ⟨86999728965838574079217475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 231999277242236197544579933 86999728965838574079217475)
      ·
        refine ⟨130499593448757861118826213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86999728965838574079217475 130499593448757861118826213)
        ·
          refine ⟨24468673771642098959779915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 130499593448757861118826213 24468673771642098959779915)
          ·
            refine ⟨36703010657463148439669873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24468673771642098959779915 36703010657463148439669873)
            ·
              refine ⟨27527257993097361329752405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36703010657463148439669873 27527257993097361329752405)
              ·
                refine ⟨80646263651652425770759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 27527257993097361329752405 80646263651652425770759)
                ·
                  rfl

theorem cell23_4240567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 10].length) (baseStart_4240567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4240567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4240567 prefixEnd_4240567 := by exact prefixLift 4240567
  have htrace : WordTrace (prefixWord ++ tailWord_4240567) baseStart_4240567 baseEnd_4240567 := by
    simpa [prefixWord, tailWord_4240567, baseEnd_4240567] using wordTrace_append hprefix tailTrace_4240567
  have hstable : (prefixWord ++ tailWord_4240567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4240567).length < 2 ^ (prefixWord ++ tailWord_4240567).sum := by decide
  have hdescent : baseEnd_4240567 < baseStart_4240567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4240567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4240584 : List Nat := [2, 1, 3, 1, 2, 1, 6, 7]
def baseStart_4240584 : Nat := 118140960795 + 4240584 * 2 ^ 59
def prefixEnd_4240584 : Nat := 4983230072969 + 3 ^ 40 * 4240584 * 2
def baseEnd_4240584 : Nat := 80646586954286738122145

theorem tailTrace_4240584 : CollatzResearch.WordTrace tailWord_4240584 prefixEnd_4240584 80646586954286738122145 := by
  unfold tailWord_4240584
  simp only [CollatzResearch.WordTrace]
  refine ⟨77333402434547938466544403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103111203246063917955392537 77333402434547938466544403)
  ·
    refine ⟨116000103651821907699816605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77333402434547938466544403 116000103651821907699816605)
    ·
      refine ⟨43500038869433215387431227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116000103651821907699816605 43500038869433215387431227)
      ·
        refine ⟨65250058304149823081146841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43500038869433215387431227 65250058304149823081146841)
        ·
          refine ⟨48937543728112367310860131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65250058304149823081146841 48937543728112367310860131)
          ·
            refine ⟨73406315592168550966290197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48937543728112367310860131 73406315592168550966290197)
            ·
              refine ⟨3440921043382900826544853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 73406315592168550966290197 3440921043382900826544853)
              ·
                refine ⟨80646586954286738122145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3440921043382900826544853 80646586954286738122145)
                ·
                  rfl

theorem cell23_4240584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 7].length) (baseStart_4240584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4240584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4240584 prefixEnd_4240584 := by exact prefixLift 4240584
  have htrace : WordTrace (prefixWord ++ tailWord_4240584) baseStart_4240584 baseEnd_4240584 := by
    simpa [prefixWord, tailWord_4240584, baseEnd_4240584] using wordTrace_append hprefix tailTrace_4240584
  have hstable : (prefixWord ++ tailWord_4240584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4240584).length < 2 ^ (prefixWord ++ tailWord_4240584).sum := by decide
  have hdescent : baseEnd_4240584 < baseStart_4240584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4240584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4240651 : List Nat := [1, 1, 1, 1, 5, 3, 1, 1, 3, 4, 2]
def baseStart_4240651 : Nat := 118140960795 + 4240651 * 2 ^ 59
def prefixEnd_4240651 : Nat := 4983230072969 + 3 ^ 40 * 4240651 * 2
def baseEnd_4240651 : Nat := 2177492250969593167160107

theorem tailTrace_4240651 : CollatzResearch.WordTrace tailWord_4240651 prefixEnd_4240651 2177492250969593167160107 := by
  unfold tailWord_4240651
  simp only [CollatzResearch.WordTrace]
  refine ⟨154669248559853147375777807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103112832373235431583851871 154669248559853147375777807)
  ·
    refine ⟨232003872839779721063666711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154669248559853147375777807 232003872839779721063666711)
    ·
      refine ⟨348005809259669581595500067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232003872839779721063666711 348005809259669581595500067)
      ·
        refine ⟨522008713889504372393250101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 348005809259669581595500067 522008713889504372393250101)
        ·
          refine ⟨48938316927141034911867197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 522008713889504372393250101 48938316927141034911867197)
          ·
            refine ⟨18351868847677888091950199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48938316927141034911867197 18351868847677888091950199)
            ·
              refine ⟨27527803271516832137925299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18351868847677888091950199 27527803271516832137925299)
              ·
                refine ⟨41291704907275248206887949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27527803271516832137925299 41291704907275248206887949)
                ·
                  refine ⟨15484389340228218077582981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41291704907275248206887949 15484389340228218077582981)
                  ·
                    refine ⟨2903323001292790889546809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15484389340228218077582981 2903323001292790889546809)
                    ·
                      refine ⟨2177492250969593167160107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2903323001292790889546809 2177492250969593167160107)
                      ·
                        rfl

theorem cell23_4240651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 4, 2].length) (baseStart_4240651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4240651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4240651 prefixEnd_4240651 := by exact prefixLift 4240651
  have htrace : WordTrace (prefixWord ++ tailWord_4240651) baseStart_4240651 baseEnd_4240651 := by
    simpa [prefixWord, tailWord_4240651, baseEnd_4240651] using wordTrace_append hprefix tailTrace_4240651
  have hstable : (prefixWord ++ tailWord_4240651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4240651).length < 2 ^ (prefixWord ++ tailWord_4240651).sum := by decide
  have hdescent : baseEnd_4240651 < baseStart_4240651 := by decide
  rcases family_descends (prefixWord ++ tailWord_4240651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4240668 : List Nat := [2, 2, 3, 1, 1, 1, 2, 3, 4, 2, 2]
def baseStart_4240668 : Nat := 118140960795 + 4240668 * 2 ^ 59
def prefixEnd_4240668 : Nat := 4983230072969 + 3 ^ 40 * 4240668 * 2
def baseEnd_4240668 : Nat := 2177500980140719600647529

theorem tailTrace_4240668 : CollatzResearch.WordTrace tailWord_4240668 prefixEnd_4240668 2177500980140719600647529 := by
  unfold tailWord_4240668
  simp only [CollatzResearch.WordTrace]
  refine ⟨77334934300395779639573329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103113245733861039519431105 77334934300395779639573329)
  ·
    refine ⟨58001200725296834729679997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77334934300395779639573329 58001200725296834729679997)
    ·
      refine ⟨21750450271986313023629999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58001200725296834729679997 21750450271986313023629999)
      ·
        refine ⟨32625675407979469535444999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21750450271986313023629999 32625675407979469535444999)
        ·
          refine ⟨48938513111969204303167499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32625675407979469535444999 48938513111969204303167499)
          ·
            refine ⟨73407769667953806454751249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48938513111969204303167499 73407769667953806454751249)
            ·
              refine ⟨55055827250965354841063437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73407769667953806454751249 55055827250965354841063437)
              ·
                refine ⟨20645935219112008065398789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55055827250965354841063437 20645935219112008065398789)
                ·
                  refine ⟨3871112853583501512262273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20645935219112008065398789 3871112853583501512262273)
                  ·
                    refine ⟨2903334640187626134196705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3871112853583501512262273 2903334640187626134196705)
                    ·
                      refine ⟨2177500980140719600647529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2903334640187626134196705 2177500980140719600647529)
                      ·
                        rfl

theorem cell23_4240668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 4, 2, 2].length) (baseStart_4240668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4240668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4240668 prefixEnd_4240668 := by exact prefixLift 4240668
  have htrace : WordTrace (prefixWord ++ tailWord_4240668) baseStart_4240668 baseEnd_4240668 := by
    simpa [prefixWord, tailWord_4240668, baseEnd_4240668] using wordTrace_append hprefix tailTrace_4240668
  have hstable : (prefixWord ++ tailWord_4240668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4240668).length < 2 ^ (prefixWord ++ tailWord_4240668).sum := by decide
  have hdescent : baseEnd_4240668 < baseStart_4240668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4240668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4240685 : List Nat := [1, 5, 3, 1, 1, 1, 1, 3, 1, 4, 2]
def baseStart_4240685 : Nat := 118140960795 + 4240685 * 2 ^ 59
def prefixEnd_4240685 : Nat := 4983230072969 + 3 ^ 40 * 4240685 * 2
def baseEnd_4240685 : Nat := 2177509709311846034134951

theorem tailTrace_4240685 : CollatzResearch.WordTrace tailWord_4240685 prefixEnd_4240685 2177509709311846034134951 := by
  unfold tailWord_4240685
  simp only [CollatzResearch.WordTrace]
  refine ⟨154670488641729971182515509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103113659094486647455010339 154670488641729971182515509)
  ·
    refine ⟨14500358310162184798360829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 154670488641729971182515509 14500358310162184798360829)
    ·
      refine ⟨5437634366310819299385311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14500358310162184798360829 5437634366310819299385311)
      ·
        refine ⟨8156451549466228949077967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5437634366310819299385311 8156451549466228949077967)
        ·
          refine ⟨12234677324199343423616951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8156451549466228949077967 12234677324199343423616951)
          ·
            refine ⟨18352015986299015135425427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12234677324199343423616951 18352015986299015135425427)
            ·
              refine ⟨27528023979448522703138141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18352015986299015135425427 27528023979448522703138141)
              ·
                refine ⟨10323008992293196013676803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27528023979448522703138141 10323008992293196013676803)
                ·
                  refine ⟨15484513488439794020515205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10323008992293196013676803 15484513488439794020515205)
                  ·
                    refine ⟨2903346279082461378846601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15484513488439794020515205 2903346279082461378846601)
                    ·
                      refine ⟨2177509709311846034134951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2903346279082461378846601 2177509709311846034134951)
                      ·
                        rfl

theorem cell23_4240685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_4240685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4240685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4240685 prefixEnd_4240685 := by exact prefixLift 4240685
  have htrace : WordTrace (prefixWord ++ tailWord_4240685) baseStart_4240685 baseEnd_4240685 := by
    simpa [prefixWord, tailWord_4240685, baseEnd_4240685] using wordTrace_append hprefix tailTrace_4240685
  have hstable : (prefixWord ++ tailWord_4240685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4240685).length < 2 ^ (prefixWord ++ tailWord_4240685).sum := by decide
  have hdescent : baseEnd_4240685 < baseStart_4240685 := by decide
  rcases family_descends (prefixWord ++ tailWord_4240685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4240704 : List Nat := [2, 1, 1, 2, 2, 1, 5, 1, 1, 7]
def baseStart_4240704 : Nat := 118140960795 + 4240704 * 2 ^ 59
def prefixEnd_4240704 : Nat := 4983230072969 + 3 ^ 40 * 4240704 * 2
def baseEnd_4240704 : Nat := 725839821814760486599121

theorem tailTrace_4240704 : CollatzResearch.WordTrace tailWord_4240704 prefixEnd_4240704 725839821814760486599121 := by
  unfold tailWord_4240704
  simp only [CollatzResearch.WordTrace]
  refine ⟨77335590814330568713728583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103114121085774091618304777 77335590814330568713728583)
  ·
    refine ⟨116003386221495853070592875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77335590814330568713728583 116003386221495853070592875)
    ·
      refine ⟨174005079332243779605889313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116003386221495853070592875 174005079332243779605889313)
      ·
        refine ⟨130503809499182834704416985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174005079332243779605889313 130503809499182834704416985)
        ·
          refine ⟨97877857124387126028312739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130503809499182834704416985 97877857124387126028312739)
          ·
            refine ⟨146816785686580689042469109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97877857124387126028312739 146816785686580689042469109)
            ·
              refine ⟨13764073658116939597731479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 146816785686580689042469109 13764073658116939597731479)
              ·
                refine ⟨20646110487175409396597219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13764073658116939597731479 20646110487175409396597219)
                ·
                  refine ⟨30969165730763114094895829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20646110487175409396597219 30969165730763114094895829)
                  ·
                    refine ⟨725839821814760486599121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30969165730763114094895829 725839821814760486599121)
                    ·
                      rfl

theorem cell23_4240704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 1, 7].length) (baseStart_4240704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4240704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4240704 prefixEnd_4240704 := by exact prefixLift 4240704
  have htrace : WordTrace (prefixWord ++ tailWord_4240704) baseStart_4240704 baseEnd_4240704 := by
    simpa [prefixWord, tailWord_4240704, baseEnd_4240704] using wordTrace_append hprefix tailTrace_4240704
  have hstable : (prefixWord ++ tailWord_4240704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4240704).length < 2 ^ (prefixWord ++ tailWord_4240704).sum := by decide
  have hdescent : baseEnd_4240704 < baseStart_4240704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4240704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4240714 : List Nat := [3, 1, 2, 1, 1, 1, 1, 3, 3, 2, 5]
def baseStart_4240714 : Nat := 118140960795 + 4240714 * 2 ^ 59
def prefixEnd_4240714 : Nat := 4983230072969 + 3 ^ 40 * 4240714 * 2
def baseEnd_4240714 : Nat := 2177524600250826420672317

theorem tailTrace_4240714 : CollatzResearch.WordTrace tailWord_4240714 prefixEnd_4240714 2177524600250826420672317 := by
  unfold tailWord_4240714
  simp only [CollatzResearch.WordTrace]
  refine ⟨38667886589656227283830299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103114364239083272756880797 38667886589656227283830299)
  ·
    refine ⟨58001829884484340925745449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38667886589656227283830299 58001829884484340925745449)
    ·
      refine ⟨43501372413363255694309087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58001829884484340925745449 43501372413363255694309087)
      ·
        refine ⟨65252058620044883541463631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43501372413363255694309087 65252058620044883541463631)
        ·
          refine ⟨97878087930067325312195447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65252058620044883541463631 97878087930067325312195447)
          ·
            refine ⟨146817131895100987968293171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97878087930067325312195447 146817131895100987968293171)
            ·
              refine ⟨220225697842651481952439757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146817131895100987968293171 220225697842651481952439757)
              ·
                refine ⟨82584636690994305732164909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 220225697842651481952439757 82584636690994305732164909)
                ·
                  refine ⟨30969238759122864649561841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82584636690994305732164909 30969238759122864649561841)
                  ·
                    refine ⟨23226929069342148487171381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30969238759122864649561841 23226929069342148487171381)
                    ·
                      refine ⟨2177524600250826420672317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23226929069342148487171381 2177524600250826420672317)
                      ·
                        rfl

theorem cell23_4240714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_4240714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4240714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4240714 prefixEnd_4240714 := by exact prefixLift 4240714
  have htrace : WordTrace (prefixWord ++ tailWord_4240714) baseStart_4240714 baseEnd_4240714 := by
    simpa [prefixWord, tailWord_4240714, baseEnd_4240714] using wordTrace_append hprefix tailTrace_4240714
  have hstable : (prefixWord ++ tailWord_4240714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4240714).length < 2 ^ (prefixWord ++ tailWord_4240714).sum := by decide
  have hdescent : baseEnd_4240714 < baseStart_4240714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4240714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4240751 : List Nat := [1, 1, 2, 1, 3, 1, 3, 4, 3, 4]
def baseStart_4240751 : Nat := 118140960795 + 4240751 * 2 ^ 59
def prefixEnd_4240751 : Nat := 4983230072969 + 3 ^ 40 * 4240751 * 2
def baseEnd_4240751 : Nat := 725847866345014258636549

theorem tailTrace_4240751 : CollatzResearch.WordTrace tailWord_4240751 prefixEnd_4240751 725847866345014258636549 := by
  unfold tailWord_4240751
  simp only [CollatzResearch.WordTrace]
  refine ⟨154672895859490864454418107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103115263906327242969612071 154672895859490864454418107)
  ·
    refine ⟨232009343789236296681627161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154672895859490864454418107 232009343789236296681627161)
    ·
      refine ⟨174007007841927222511220371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232009343789236296681627161 174007007841927222511220371)
      ·
        refine ⟨261010511762890833766830557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174007007841927222511220371 261010511762890833766830557)
        ·
          refine ⟨97878941911084062662561459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 261010511762890833766830557 97878941911084062662561459)
          ·
            refine ⟨146818412866626093993842189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97878941911084062662561459 146818412866626093993842189)
            ·
              refine ⟨55056904824984785247690821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 146818412866626093993842189 55056904824984785247690821)
              ·
                refine ⟨10323169654684647233942029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55056904824984785247690821 10323169654684647233942029)
                ·
                  refine ⟨3871188620506742712728261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10323169654684647233942029 3871188620506742712728261)
                  ·
                    refine ⟨725847866345014258636549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3871188620506742712728261 725847866345014258636549)
                    ·
                      rfl

theorem cell23_4240751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 3, 4].length) (baseStart_4240751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4240751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4240751 prefixEnd_4240751 := by exact prefixLift 4240751
  have htrace : WordTrace (prefixWord ++ tailWord_4240751) baseStart_4240751 baseEnd_4240751 := by
    simpa [prefixWord, tailWord_4240751, baseEnd_4240751] using wordTrace_append hprefix tailTrace_4240751
  have hstable : (prefixWord ++ tailWord_4240751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4240751).length < 2 ^ (prefixWord ++ tailWord_4240751).sum := by decide
  have hdescent : baseEnd_4240751 < baseStart_4240751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4240751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4240761 : List Nat := [1, 2, 1, 3, 2, 1, 4, 1, 1, 4, 3]
def baseStart_4240761 : Nat := 118140960795 + 4240761 * 2 ^ 59
def prefixEnd_4240761 : Nat := 4983230072969 + 3 ^ 40 * 4240761 * 2
def baseEnd_4240761 : Nat := 2177548733841587736784601

theorem tailTrace_4240761 : CollatzResearch.WordTrace tailWord_4240761 prefixEnd_4240761 2177548733841587736784601 := by
  unfold tailWord_4240761
  simp only [CollatzResearch.WordTrace]
  refine ⟨154673260589454636162282137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103115507059636424108188091 154673260589454636162282137)
  ·
    refine ⟨116004945442090977121711603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154673260589454636162282137 116004945442090977121711603)
    ·
      refine ⟨174007418163136465682567405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116004945442090977121711603 174007418163136465682567405)
      ·
        refine ⟨65252781811176174630962777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 174007418163136465682567405 65252781811176174630962777)
        ·
          refine ⟨48939586358382130973222083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65252781811176174630962777 48939586358382130973222083)
          ·
            refine ⟨73409379537573196459833125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48939586358382130973222083 73409379537573196459833125)
            ·
              refine ⟨13764258663294974336218711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73409379537573196459833125 13764258663294974336218711)
              ·
                refine ⟨20646387994942461504328067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13764258663294974336218711 20646387994942461504328067)
                ·
                  refine ⟨30969581992413692256492101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20646387994942461504328067 30969581992413692256492101)
                  ·
                    refine ⟨5806796623577567298092269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30969581992413692256492101 5806796623577567298092269)
                    ·
                      refine ⟨2177548733841587736784601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5806796623577567298092269 2177548733841587736784601)
                      ·
                        rfl

theorem cell23_4240761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 4, 3].length) (baseStart_4240761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4240761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4240761 prefixEnd_4240761 := by exact prefixLift 4240761
  have htrace : WordTrace (prefixWord ++ tailWord_4240761) baseStart_4240761 baseEnd_4240761 := by
    simpa [prefixWord, tailWord_4240761, baseEnd_4240761] using wordTrace_append hprefix tailTrace_4240761
  have hstable : (prefixWord ++ tailWord_4240761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4240761).length < 2 ^ (prefixWord ++ tailWord_4240761).sum := by decide
  have hdescent : baseEnd_4240761 < baseStart_4240761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4240761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4240764 : List Nat := [2, 2, 2, 1, 1, 1, 3, 1, 10]
def baseStart_4240764 : Nat := 118140960795 + 4240764 * 2 ^ 59
def prefixEnd_4240764 : Nat := 4983230072969 + 3 ^ 40 * 4240764 * 2
def baseEnd_4240764 : Nat := 241950030475950136116343

theorem tailTrace_4240764 : CollatzResearch.WordTrace tailWord_4240764 prefixEnd_4240764 241950030475950136116343 := by
  unfold tailWord_4240764
  simp only [CollatzResearch.WordTrace]
  refine ⟨77336685004221883837320673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103115580005629178449760897 77336685004221883837320673)
  ·
    refine ⟨58002513753166412877990505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77336685004221883837320673 58002513753166412877990505)
    ·
      refine ⟨43501885314874809658492879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58002513753166412877990505 43501885314874809658492879)
      ·
        refine ⟨65252827972312214487739319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43501885314874809658492879 65252827972312214487739319)
        ·
          refine ⟨97879241958468321731608979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65252827972312214487739319 97879241958468321731608979)
          ·
            refine ⟨146818862937702482597413469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97879241958468321731608979 146818862937702482597413469)
            ·
              refine ⟨55057073601638430974030051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 146818862937702482597413469 55057073601638430974030051)
              ·
                refine ⟨82585610402457646461045077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55057073601638430974030051 82585610402457646461045077)
                ·
                  refine ⟨241950030475950136116343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 82585610402457646461045077 241950030475950136116343)
                  ·
                    rfl

theorem cell23_4240764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 10].length) (baseStart_4240764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4240764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4240764 prefixEnd_4240764 := by exact prefixLift 4240764
  have htrace : WordTrace (prefixWord ++ tailWord_4240764) baseStart_4240764 baseEnd_4240764 := by
    simpa [prefixWord, tailWord_4240764, baseEnd_4240764] using wordTrace_append hprefix tailTrace_4240764
  have hstable : (prefixWord ++ tailWord_4240764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4240764).length < 2 ^ (prefixWord ++ tailWord_4240764).sum := by decide
  have hdescent : baseEnd_4240764 < baseStart_4240764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4240764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4240842 : List Nat := [3, 1, 2, 1, 2, 4, 1, 4, 1, 1, 3]
def baseStart_4240842 : Nat := 118140960795 + 4240842 * 2 ^ 59
def prefixEnd_4240842 : Nat := 4983230072969 + 3 ^ 40 * 4240842 * 2
def baseEnd_4240842 : Nat := 2177590325774601919871729

theorem tailTrace_4240842 : CollatzResearch.WordTrace tailWord_4240842 prefixEnd_4240842 2177590325774601919871729 := by
  unfold tailWord_4240842
  simp only [CollatzResearch.WordTrace]
  refine ⟨38669053725540296748995195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103117476601440791330653853 38669053725540296748995195)
  ·
    refine ⟨58003580588310445123492793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38669053725540296748995195 58003580588310445123492793)
    ·
      refine ⟨43502685441232833842619595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58003580588310445123492793 43502685441232833842619595)
      ·
        refine ⟨65254028161849250763929393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43502685441232833842619595 65254028161849250763929393)
        ·
          refine ⟨48940521121386938072947045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65254028161849250763929393 48940521121386938072947045)
          ·
            refine ⟨9176347710260050888677571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48940521121386938072947045 9176347710260050888677571)
            ·
              refine ⟨13764521565390076333016357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9176347710260050888677571 13764521565390076333016357)
              ·
                refine ⟨2580847793510639312440567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13764521565390076333016357 2580847793510639312440567)
                ·
                  refine ⟨3871271690265958968660851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2580847793510639312440567 3871271690265958968660851)
                  ·
                    refine ⟨5806907535398938452991277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3871271690265958968660851 5806907535398938452991277)
                    ·
                      refine ⟨2177590325774601919871729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5806907535398938452991277 2177590325774601919871729)
                      ·
                        rfl

theorem cell23_4240842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 4, 1, 1, 3].length) (baseStart_4240842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4240842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4240842 prefixEnd_4240842 := by exact prefixLift 4240842
  have htrace : WordTrace (prefixWord ++ tailWord_4240842) baseStart_4240842 baseEnd_4240842 := by
    simpa [prefixWord, tailWord_4240842, baseEnd_4240842] using wordTrace_append hprefix tailTrace_4240842
  have hstable : (prefixWord ++ tailWord_4240842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4240842).length < 2 ^ (prefixWord ++ tailWord_4240842).sum := by decide
  have hdescent : baseEnd_4240842 < baseStart_4240842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4240842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4240858 : List Nat := [3, 1, 1, 2, 3, 3, 2, 1, 1, 6]
def baseStart_4240858 : Nat := 118140960795 + 4240858 * 2 ^ 59
def prefixEnd_4240858 : Nat := 4983230072969 + 3 ^ 40 * 4240858 * 2
def baseEnd_4240858 : Nat := 725866180488357952423885

theorem tailTrace_4240858 : CollatzResearch.WordTrace tailWord_4240858 prefixEnd_4240858 725866180488357952423885 := by
  unfold tailWord_4240858
  simp only [CollatzResearch.WordTrace]
  refine ⟨38669199617525805432140807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103117865646735481152375485 38669199617525805432140807)
  ·
    refine ⟨58003799426288708148211211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38669199617525805432140807 58003799426288708148211211)
    ·
      refine ⟨87005699139433062222316817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58003799426288708148211211 87005699139433062222316817)
      ·
        refine ⟨65254274354574796666737613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87005699139433062222316817 65254274354574796666737613)
        ·
          refine ⟨24470352882965548750026605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65254274354574796666737613 24470352882965548750026605)
          ·
            refine ⟨9176382331112080781259977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24470352882965548750026605 9176382331112080781259977)
            ·
              refine ⟨6882286748334060585944983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9176382331112080781259977 6882286748334060585944983)
              ·
                refine ⟨10323430122501090878917475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6882286748334060585944983 10323430122501090878917475)
                ·
                  refine ⟨15485145183751636318376213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10323430122501090878917475 15485145183751636318376213)
                  ·
                    refine ⟨725866180488357952423885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15485145183751636318376213 725866180488357952423885)
                    ·
                      rfl

theorem cell23_4240858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 1, 6].length) (baseStart_4240858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4240858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4240858 prefixEnd_4240858 := by exact prefixLift 4240858
  have htrace : WordTrace (prefixWord ++ tailWord_4240858) baseStart_4240858 baseEnd_4240858 := by
    simpa [prefixWord, tailWord_4240858, baseEnd_4240858] using wordTrace_append hprefix tailTrace_4240858
  have hstable : (prefixWord ++ tailWord_4240858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4240858).length < 2 ^ (prefixWord ++ tailWord_4240858).sum := by decide
  have hdescent : baseEnd_4240858 < baseStart_4240858 := by decide
  rcases family_descends (prefixWord ++ tailWord_4240858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4240865 : List Nat := [1, 2, 3, 1, 2, 3, 1, 1, 5, 2, 2]
def baseStart_4240865 : Nat := 118140960795 + 4240865 * 2 ^ 59
def prefixEnd_4240865 : Nat := 4983230072969 + 3 ^ 40 * 4240865 * 2
def baseEnd_4240865 : Nat := 2177602135829655329884123

theorem tailTrace_4240865 : CollatzResearch.WordTrace tailWord_4240865 prefixEnd_4240865 2177602135829655329884123 := by
  unfold tailWord_4240865
  simp only [CollatzResearch.WordTrace]
  refine ⟨154677053781077861924068049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103118035854051907949378699 154677053781077861924068049)
  ·
    refine ⟨116007790335808396443051037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154677053781077861924068049 116007790335808396443051037)
    ·
      refine ⟨43502921375928148666144139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116007790335808396443051037 43502921375928148666144139)
      ·
        refine ⟨65254382063892222999216209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43502921375928148666144139 65254382063892222999216209)
        ·
          refine ⟨48940786547919167249412157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65254382063892222999216209 48940786547919167249412157)
          ·
            refine ⟨18352794955469687718529559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48940786547919167249412157 18352794955469687718529559)
            ·
              refine ⟨27529192433204531577794339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18352794955469687718529559 27529192433204531577794339)
              ·
                refine ⟨41293788649806797366691509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27529192433204531577794339 41293788649806797366691509)
                ·
                  refine ⟨3871292685919387253127329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41293788649806797366691509 3871292685919387253127329)
                  ·
                    refine ⟨2903469514439540439845497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3871292685919387253127329 2903469514439540439845497)
                    ·
                      refine ⟨2177602135829655329884123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2903469514439540439845497 2177602135829655329884123)
                      ·
                        rfl

theorem cell23_4240865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 5, 2, 2].length) (baseStart_4240865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4240865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4240865 prefixEnd_4240865 := by exact prefixLift 4240865
  have htrace : WordTrace (prefixWord ++ tailWord_4240865) baseStart_4240865 baseEnd_4240865 := by
    simpa [prefixWord, tailWord_4240865, baseEnd_4240865] using wordTrace_append hprefix tailTrace_4240865
  have hstable : (prefixWord ++ tailWord_4240865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4240865).length < 2 ^ (prefixWord ++ tailWord_4240865).sum := by decide
  have hdescent : baseEnd_4240865 < baseStart_4240865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4240865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4240878 : List Nat := [4, 1, 2, 1, 2, 1, 1, 4, 1, 2, 4]
def baseStart_4240878 : Nat := 118140960795 + 4240878 * 2 ^ 59
def prefixEnd_4240878 : Nat := 4983230072969 + 3 ^ 40 * 4240878 * 2
def baseEnd_4240878 : Nat := 2177608811078163779021563

theorem tailTrace_4240878 : CollatzResearch.WordTrace tailWord_4240878 prefixEnd_4240878 2177608811078163779021563 := by
  unfold tailWord_4240878
  simp only [CollatzResearch.WordTrace]
  refine ⟨19334690991253845643036411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103118351953353843429527525 19334690991253845643036411)
  ·
    refine ⟨29002036486880768464554617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19334690991253845643036411 29002036486880768464554617)
    ·
      refine ⟨21751527365160576348415963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29002036486880768464554617 21751527365160576348415963)
      ·
        refine ⟨32627291047740864522623945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21751527365160576348415963 32627291047740864522623945)
        ·
          refine ⟨24470468285805648391967959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32627291047740864522623945 24470468285805648391967959)
          ·
            refine ⟨36705702428708472587951939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24470468285805648391967959 36705702428708472587951939)
            ·
              refine ⟨55058553643062708881927909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36705702428708472587951939 55058553643062708881927909)
              ·
                refine ⟨10323478808074257915361483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55058553643062708881927909 10323478808074257915361483)
                ·
                  refine ⟨15485218212111386873042225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10323478808074257915361483 15485218212111386873042225)
                  ·
                    refine ⟨11613913659083540154781669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15485218212111386873042225 11613913659083540154781669)
                    ·
                      refine ⟨2177608811078163779021563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11613913659083540154781669 2177608811078163779021563)
                      ·
                        rfl

theorem cell23_4240878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_4240878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4240878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4240878 prefixEnd_4240878 := by exact prefixLift 4240878
  have htrace : WordTrace (prefixWord ++ tailWord_4240878) baseStart_4240878 baseEnd_4240878 := by
    simpa [prefixWord, tailWord_4240878, baseEnd_4240878] using wordTrace_append hprefix tailTrace_4240878
  have hstable : (prefixWord ++ tailWord_4240878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4240878).length < 2 ^ (prefixWord ++ tailWord_4240878).sum := by decide
  have hdescent : baseEnd_4240878 < baseStart_4240878 := by decide
  rcases family_descends (prefixWord ++ tailWord_4240878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4240882 : List Nat := [3, 2, 1, 4, 1, 1, 4, 1, 1, 1, 4]
def baseStart_4240882 : Nat := 118140960795 + 4240882 * 2 ^ 59
def prefixEnd_4240882 : Nat := 4983230072969 + 3 ^ 40 * 4240882 * 2
def baseEnd_4240882 : Nat := 2177610865000781763371545

theorem tailTrace_4240882 : CollatzResearch.WordTrace tailWord_4240882 prefixEnd_4240882 2177610865000781763371545 := by
  unfold tailWord_4240882
  simp only [CollatzResearch.WordTrace]
  refine ⟨38669418455504068456859225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103118449214677515884957933 38669418455504068456859225)
  ·
    refine ⟨29002063841628051342644419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38669418455504068456859225 29002063841628051342644419)
    ·
      refine ⟨43503095762442077013966629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29002063841628051342644419 43503095762442077013966629)
      ·
        refine ⟨8156830455457889440118743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43503095762442077013966629 8156830455457889440118743)
        ·
          refine ⟨12235245683186834160178115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8156830455457889440118743 12235245683186834160178115)
          ·
            refine ⟨18352868524780251240267173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12235245683186834160178115 18352868524780251240267173)
            ·
              refine ⟨3441162848396297107550095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18352868524780251240267173 3441162848396297107550095)
              ·
                refine ⟨5161744272594445661325143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3441162848396297107550095 5161744272594445661325143)
                ·
                  refine ⟨7742616408891668491987715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5161744272594445661325143 7742616408891668491987715)
                  ·
                    refine ⟨11613924613337502737981573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7742616408891668491987715 11613924613337502737981573)
                    ·
                      refine ⟨2177610865000781763371545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11613924613337502737981573 2177610865000781763371545)
                      ·
                        rfl

theorem cell23_4240882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_4240882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4240882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4240882 prefixEnd_4240882 := by exact prefixLift 4240882
  have htrace : WordTrace (prefixWord ++ tailWord_4240882) baseStart_4240882 baseEnd_4240882 := by
    simpa [prefixWord, tailWord_4240882, baseEnd_4240882] using wordTrace_append hprefix tailTrace_4240882
  have hstable : (prefixWord ++ tailWord_4240882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4240882).length < 2 ^ (prefixWord ++ tailWord_4240882).sum := by decide
  have hdescent : baseEnd_4240882 < baseStart_4240882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4240882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4240909 : List Nat := [1, 7, 1, 1, 2, 2, 1, 1, 1, 6]
def baseStart_4240909 : Nat := 118140960795 + 4240909 * 2 ^ 59
def prefixEnd_4240909 : Nat := 4983230072969 + 3 ^ 40 * 4240909 * 2
def baseEnd_4240909 : Nat := 725874909659484385911307

theorem tailTrace_4240909 : CollatzResearch.WordTrace tailWord_4240909 prefixEnd_4240909 725874909659484385911307 := by
  unfold tailWord_4240909
  simp only [CollatzResearch.WordTrace]
  refine ⟨154678658592918457438669781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103119105728612304959113187 154678658592918457438669781)
  ·
    refine ⟨3625281060771526346218823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 154678658592918457438669781 3625281060771526346218823)
    ·
      refine ⟨5437921591157289519328235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3625281060771526346218823 5437921591157289519328235)
      ·
        refine ⟨8156882386735934278992353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5437921591157289519328235 8156882386735934278992353)
        ·
          refine ⟨6117661790051950709244265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8156882386735934278992353 6117661790051950709244265)
          ·
            refine ⟨4588246342538963031933199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6117661790051950709244265 4588246342538963031933199)
            ·
              refine ⟨6882369513808444547899799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4588246342538963031933199 6882369513808444547899799)
              ·
                refine ⟨10323554270712666821849699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6882369513808444547899799 10323554270712666821849699)
                ·
                  refine ⟨15485331406069000232774549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10323554270712666821849699 15485331406069000232774549)
                  ·
                    refine ⟨725874909659484385911307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15485331406069000232774549 725874909659484385911307)
                    ·
                      rfl

theorem cell23_4240909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_4240909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4240909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4240909 prefixEnd_4240909 := by exact prefixLift 4240909
  have htrace : WordTrace (prefixWord ++ tailWord_4240909) baseStart_4240909 baseEnd_4240909 := by
    simpa [prefixWord, tailWord_4240909, baseEnd_4240909] using wordTrace_append hprefix tailTrace_4240909
  have hstable : (prefixWord ++ tailWord_4240909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4240909).length < 2 ^ (prefixWord ++ tailWord_4240909).sum := by decide
  have hdescent : baseEnd_4240909 < baseStart_4240909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4240909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4240915 : List Nat := [1, 1, 1, 2, 1, 8, 1, 1, 1, 3, 3]
def baseStart_4240915 : Nat := 118140960795 + 4240915 * 2 ^ 59
def prefixEnd_4240915 : Nat := 4983230072969 + 3 ^ 40 * 4240915 * 2
def baseEnd_4240915 : Nat := 2177627809862380134258893

theorem tailTrace_4240915 : CollatzResearch.WordTrace tailWord_4240915 prefixEnd_4240915 2177627809862380134258893 := by
  unfold tailWord_4240915
  simp only [CollatzResearch.WordTrace]
  refine ⟨154678877430896720463388199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103119251620597813642258799 154678877430896720463388199)
  ·
    refine ⟨232018316146345080695082299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154678877430896720463388199 232018316146345080695082299)
    ·
      refine ⟨348027474219517621042623449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232018316146345080695082299 348027474219517621042623449)
      ·
        refine ⟨261020605664638215781967587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 348027474219517621042623449 261020605664638215781967587)
        ·
          refine ⟨391530908496957323672951381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261020605664638215781967587 391530908496957323672951381)
          ·
            refine ⟨4588252833948718636792399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 391530908496957323672951381 4588252833948718636792399)
            ·
              refine ⟨6882379250923077955188599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4588252833948718636792399 6882379250923077955188599)
              ·
                refine ⟨10323568876384616932782899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6882379250923077955188599 10323568876384616932782899)
                ·
                  refine ⟨15485353314576925399174349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10323568876384616932782899 15485353314576925399174349)
                  ·
                    refine ⟨5807007492966347024690381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15485353314576925399174349 5807007492966347024690381)
                    ·
                      refine ⟨2177627809862380134258893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5807007492966347024690381 2177627809862380134258893)
                      ·
                        rfl

theorem cell23_4240915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 3, 3].length) (baseStart_4240915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4240915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4240915 prefixEnd_4240915 := by exact prefixLift 4240915
  have htrace : WordTrace (prefixWord ++ tailWord_4240915) baseStart_4240915 baseEnd_4240915 := by
    simpa [prefixWord, tailWord_4240915, baseEnd_4240915] using wordTrace_append hprefix tailTrace_4240915
  have hstable : (prefixWord ++ tailWord_4240915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4240915).length < 2 ^ (prefixWord ++ tailWord_4240915).sum := by decide
  have hdescent : baseEnd_4240915 < baseStart_4240915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4240915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4240928 : List Nat := [2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 5]
def baseStart_4240928 : Nat := 118140960795 + 4240928 * 2 ^ 59
def prefixEnd_4240928 : Nat := 4983230072969 + 3 ^ 40 * 4240928 * 2
def baseEnd_4240928 : Nat := 2177634485110888583396333

theorem tailTrace_4240928 : CollatzResearch.WordTrace tailWord_4240928 prefixEnd_4240928 2177634485110888583396333 := by
  unfold tailWord_4240928
  simp only [CollatzResearch.WordTrace]
  refine ⟨77339675789924811841805719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103119567719899749122407625 77339675789924811841805719)
  ·
    refine ⟨116009513684887217762708579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77339675789924811841805719 116009513684887217762708579)
    ·
      refine ⟨174014270527330826644062869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116009513684887217762708579 174014270527330826644062869)
      ·
        refine ⟨8156918930968632498940447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 174014270527330826644062869 8156918930968632498940447)
        ·
          refine ⟨12235378396452948748410671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8156918930968632498940447 12235378396452948748410671)
          ·
            refine ⟨18353067594679423122616007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12235378396452948748410671 18353067594679423122616007)
            ·
              refine ⟨27529601392019134683924011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18353067594679423122616007 27529601392019134683924011)
              ·
                refine ⟨41294402088028702025886017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27529601392019134683924011 41294402088028702025886017)
                ·
                  refine ⟨30970801566021526519414513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41294402088028702025886017 30970801566021526519414513)
                  ·
                    refine ⟨23228101174516144889560885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30970801566021526519414513 23228101174516144889560885)
                    ·
                      refine ⟨2177634485110888583396333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23228101174516144889560885 2177634485110888583396333)
                      ·
                        rfl

theorem cell23_4240928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_4240928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4240928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4240928 prefixEnd_4240928 := by exact prefixLift 4240928
  have htrace : WordTrace (prefixWord ++ tailWord_4240928) baseStart_4240928 baseEnd_4240928 := by
    simpa [prefixWord, tailWord_4240928, baseEnd_4240928] using wordTrace_append hprefix tailTrace_4240928
  have hstable : (prefixWord ++ tailWord_4240928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4240928).length < 2 ^ (prefixWord ++ tailWord_4240928).sum := by decide
  have hdescent : baseEnd_4240928 < baseStart_4240928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4240928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4240966 : List Nat := [6, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3]
def baseStart_4240966 : Nat := 118140960795 + 4240966 * 2 ^ 59
def prefixEnd_4240966 : Nat := 4983230072969 + 3 ^ 40 * 4240966 * 2
def baseEnd_4240966 : Nat := 2177653997375759434721159

theorem tailTrace_4240966 : CollatzResearch.WordTrace tailWord_4240966 prefixEnd_4240966 2177653997375759434721159 := by
  unfold tailWord_4240966
  simp only [CollatzResearch.WordTrace]
  refine ⟨4833773048553498630421711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 103120491702474637448996501 4833773048553498630421711)
  ·
    refine ⟨7250659572830247945632567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4833773048553498630421711 7250659572830247945632567)
    ·
      refine ⟨10875989359245371918448851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7250659572830247945632567 10875989359245371918448851)
      ·
        refine ⟨16313984038868057877673277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10875989359245371918448851 16313984038868057877673277)
        ·
          refine ⟨6117744014575521704127479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16313984038868057877673277 6117744014575521704127479)
          ·
            refine ⟨9176616021863282556191219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6117744014575521704127479 9176616021863282556191219)
            ·
              refine ⟨13764924032794923834286829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9176616021863282556191219 13764924032794923834286829)
              ·
                refine ⟨5161846512298096437857561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13764924032794923834286829 5161846512298096437857561)
                ·
                  refine ⟨3871384884223572328393171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5161846512298096437857561 3871384884223572328393171)
                  ·
                    refine ⟨5807077326335358492589757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3871384884223572328393171 5807077326335358492589757)
                    ·
                      refine ⟨2177653997375759434721159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5807077326335358492589757 2177653997375759434721159)
                      ·
                        rfl

theorem cell23_4240966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_4240966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4240966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4240966 prefixEnd_4240966 := by exact prefixLift 4240966
  have htrace : WordTrace (prefixWord ++ tailWord_4240966) baseStart_4240966 baseEnd_4240966 := by
    simpa [prefixWord, tailWord_4240966, baseEnd_4240966] using wordTrace_append hprefix tailTrace_4240966
  have hstable : (prefixWord ++ tailWord_4240966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4240966).length < 2 ^ (prefixWord ++ tailWord_4240966).sum := by decide
  have hdescent : baseEnd_4240966 < baseStart_4240966 := by decide
  rcases family_descends (prefixWord ++ tailWord_4240966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4241006 : List Nat := [4, 1, 2, 2, 3, 1, 2, 2, 2, 2, 2]
def baseStart_4241006 : Nat := 118140960795 + 4241006 * 2 ^ 59
def prefixEnd_4241006 : Nat := 4983230072969 + 3 ^ 40 * 4241006 * 2
def baseEnd_4241006 : Nat := 2177674536601939278220975

theorem tailTrace_4241006 : CollatzResearch.WordTrace tailWord_4241006 prefixEnd_4241006 2177674536601939278220975 := by
  unfold tailWord_4241006
  simp only [CollatzResearch.WordTrace]
  refine ⟨19335274559195880375618859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103121464315711362003300581 19335274559195880375618859)
  ·
    refine ⟨29002911838793820563428289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19335274559195880375618859 29002911838793820563428289)
    ·
      refine ⟨21752183879095365422571217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29002911838793820563428289 21752183879095365422571217)
      ·
        refine ⟨16314137909321524066928413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21752183879095365422571217 16314137909321524066928413)
        ·
          refine ⟨6117801715995571525098155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16314137909321524066928413 6117801715995571525098155)
          ·
            refine ⟨9176702573993357287647233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6117801715995571525098155 9176702573993357287647233)
            ·
              refine ⟨6882526930495017965735425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9176702573993357287647233 6882526930495017965735425)
              ·
                refine ⟨5161895197871263474301569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6882526930495017965735425 5161895197871263474301569)
                ·
                  refine ⟨3871421398403447605726177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5161895197871263474301569 3871421398403447605726177)
                  ·
                    refine ⟨2903566048802585704294633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3871421398403447605726177 2903566048802585704294633)
                    ·
                      refine ⟨2177674536601939278220975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2903566048802585704294633 2177674536601939278220975)
                      ·
                        rfl

theorem cell23_4241006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_4241006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4241006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4241006 prefixEnd_4241006 := by exact prefixLift 4241006
  have htrace : WordTrace (prefixWord ++ tailWord_4241006) baseStart_4241006 baseEnd_4241006 := by
    simpa [prefixWord, tailWord_4241006, baseEnd_4241006] using wordTrace_append hprefix tailTrace_4241006
  have hstable : (prefixWord ++ tailWord_4241006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4241006).length < 2 ^ (prefixWord ++ tailWord_4241006).sum := by decide
  have hdescent : baseEnd_4241006 < baseStart_4241006 := by decide
  rcases family_descends (prefixWord ++ tailWord_4241006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4241072 : List Nat := [2, 1, 1, 1, 2, 1, 6, 4, 1, 4]
def baseStart_4241072 : Nat := 118140960795 + 4241072 * 2 ^ 59
def prefixEnd_4241072 : Nat := 4983230072969 + 3 ^ 40 * 4241072 * 2
def baseEnd_4241072 : Nat := 725902808775045339998557

theorem tailTrace_4241072 : CollatzResearch.WordTrace tailWord_4241072 prefixEnd_4241072 725902808775045339998557 := by
  unfold tailWord_4241072
  simp only [CollatzResearch.WordTrace]
  refine ⟨77342301845663968138426735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103123069127551957517902313 77342301845663968138426735)
  ·
    refine ⟨116013452768495952207640103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77342301845663968138426735 116013452768495952207640103)
    ·
      refine ⟨174020179152743928311460155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116013452768495952207640103 174020179152743928311460155)
      ·
        refine ⟨261030268729115892467190233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174020179152743928311460155 261030268729115892467190233)
        ·
          refine ⟨195772701546836919350392675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 261030268729115892467190233 195772701546836919350392675)
          ·
            refine ⟨293659052320255379025589013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195772701546836919350392675 293659052320255379025589013)
            ·
              refine ⟨13765268077511970891824485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 293659052320255379025589013 13765268077511970891824485)
              ·
                refine ⟨2580987764533494542217091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13765268077511970891824485 2580987764533494542217091)
                ·
                  refine ⟨3871481646800241813325637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2580987764533494542217091 3871481646800241813325637)
                  ·
                    refine ⟨725902808775045339998557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3871481646800241813325637 725902808775045339998557)
                    ·
                      rfl

theorem cell23_4241072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 4, 1, 4].length) (baseStart_4241072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4241072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4241072 prefixEnd_4241072 := by exact prefixLift 4241072
  have htrace : WordTrace (prefixWord ++ tailWord_4241072) baseStart_4241072 baseEnd_4241072 := by
    simpa [prefixWord, tailWord_4241072, baseEnd_4241072] using wordTrace_append hprefix tailTrace_4241072
  have hstable : (prefixWord ++ tailWord_4241072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4241072).length < 2 ^ (prefixWord ++ tailWord_4241072).sum := by decide
  have hdescent : baseEnd_4241072 < baseStart_4241072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4241072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4241088 : List Nat := [2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 6]
def baseStart_4241088 : Nat := 118140960795 + 4241088 * 2 ^ 59
def prefixEnd_4241088 : Nat := 4983230072969 + 3 ^ 40 * 4241088 * 2
def baseEnd_4241088 : Nat := 2177716642015607957395597

theorem tailTrace_4241088 : CollatzResearch.WordTrace tailWord_4241088 prefixEnd_4241088 2177716642015607957395597 := by
  unfold tailWord_4241088
  simp only [CollatzResearch.WordTrace]
  refine ⟨77342593629634985504717959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103123458172846647339623945 77342593629634985504717959)
  ·
    refine ⟨116013890444452478257076939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77342593629634985504717959 116013890444452478257076939)
    ·
      refine ⟨174020835666678717385615409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116013890444452478257076939 174020835666678717385615409)
      ·
        refine ⟨130515626750009038039211557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174020835666678717385615409 130515626750009038039211557)
        ·
          refine ⟨24471680015626694632352167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 130515626750009038039211557 24471680015626694632352167)
          ·
            refine ⟨36707520023440041948528251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24471680015626694632352167 36707520023440041948528251)
            ·
              refine ⟨55061280035160062922792377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36707520023440041948528251 55061280035160062922792377)
              ·
                refine ⟨41295960026370047192094283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55061280035160062922792377 41295960026370047192094283)
                ·
                  refine ⟨61943940039555070788141425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41295960026370047192094283 61943940039555070788141425)
                  ·
                    refine ⟨46457955029666303091106069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61943940039555070788141425 46457955029666303091106069)
                    ·
                      refine ⟨2177716642015607957395597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46457955029666303091106069 2177716642015607957395597)
                      ·
                        rfl

theorem cell23_4241088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 6].length) (baseStart_4241088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4241088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4241088 prefixEnd_4241088 := by exact prefixLift 4241088
  have htrace : WordTrace (prefixWord ++ tailWord_4241088) baseStart_4241088 baseEnd_4241088 := by
    simpa [prefixWord, tailWord_4241088, baseEnd_4241088] using wordTrace_append hprefix tailTrace_4241088
  have hstable : (prefixWord ++ tailWord_4241088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4241088).length < 2 ^ (prefixWord ++ tailWord_4241088).sum := by decide
  have hdescent : baseEnd_4241088 < baseStart_4241088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4241088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4241106 : List Nat := [3, 2, 2, 2, 2, 3, 1, 3, 1, 4]
def baseStart_4241106 : Nat := 118140960795 + 4241106 * 2 ^ 59
def prefixEnd_4241106 : Nat := 4983230072969 + 3 ^ 40 * 4241106 * 2
def baseEnd_4241106 : Nat := 725908628222462962323505

theorem tailTrace_4241106 : CollatzResearch.WordTrace tailWord_4241106 prefixEnd_4241106 725908628222462962323505 := by
  unfold tailWord_4241106
  simp only [CollatzResearch.WordTrace]
  refine ⟨38671460943301190020897793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103123895848803173389060781 38671460943301190020897793)
  ·
    refine ⟨29003595707475892515673345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38671460943301190020897793 29003595707475892515673345)
    ·
      refine ⟨21752696780606919386755009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29003595707475892515673345 21752696780606919386755009)
      ·
        refine ⟨16314522585455189540066257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21752696780606919386755009 16314522585455189540066257)
        ·
          refine ⟨12235891939091392155049693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16314522585455189540066257 12235891939091392155049693)
          ·
            refine ⟨4588459477159272058143635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12235891939091392155049693 4588459477159272058143635)
            ·
              refine ⟨6882689215738908087215453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4588459477159272058143635 6882689215738908087215453)
              ·
                refine ⟨2581008455902090532705795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6882689215738908087215453 2581008455902090532705795)
                ·
                  refine ⟨3871512683853135799058693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2581008455902090532705795 3871512683853135799058693)
                  ·
                    refine ⟨725908628222462962323505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3871512683853135799058693 725908628222462962323505)
                    ·
                      rfl

theorem cell23_4241106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_4241106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4241106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4241106 prefixEnd_4241106 := by exact prefixLift 4241106
  have htrace : WordTrace (prefixWord ++ tailWord_4241106) baseStart_4241106 baseEnd_4241106 := by
    simpa [prefixWord, tailWord_4241106, baseEnd_4241106] using wordTrace_append hprefix tailTrace_4241106
  have hstable : (prefixWord ++ tailWord_4241106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4241106).length < 2 ^ (prefixWord ++ tailWord_4241106).sum := by decide
  have hdescent : baseEnd_4241106 < baseStart_4241106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4241106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4241135 : List Nat := [1, 1, 2, 1, 5, 1, 2, 2, 3, 1, 4]
def baseStart_4241135 : Nat := 118140960795 + 4241135 * 2 ^ 59
def prefixEnd_4241135 : Nat := 4983230072969 + 3 ^ 40 * 4241135 * 2
def baseEnd_4241135 : Nat := 2177740775606369273507881

theorem tailTrace_4241135 : CollatzResearch.WordTrace tailWord_4241135 prefixEnd_4241135 2177740775606369273507881 := by
  unfold tailWord_4241135
  simp only [CollatzResearch.WordTrace]
  refine ⟨154686901490099698036396859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103124600993399798690931239 154686901490099698036396859)
  ·
    refine ⟨232030352235149547054595289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154686901490099698036396859 232030352235149547054595289)
    ·
      refine ⟨174022764176362160290946467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232030352235149547054595289 174022764176362160290946467)
      ·
        refine ⟨261034146264543240436419701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174022764176362160290946467 261034146264543240436419701)
        ·
          refine ⟨24471951212300928790914347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 261034146264543240436419701 24471951212300928790914347)
          ·
            refine ⟨36707926818451393186371521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24471951212300928790914347 36707926818451393186371521)
            ·
              refine ⟨27530945113838544889778641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36707926818451393186371521 27530945113838544889778641)
              ·
                refine ⟨20648208835378908667333981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27530945113838544889778641 20648208835378908667333981)
                ·
                  refine ⟨7743078313267090750250243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20648208835378908667333981 7743078313267090750250243)
                  ·
                    refine ⟨11614617469900636125375365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7743078313267090750250243 11614617469900636125375365)
                    ·
                      refine ⟨2177740775606369273507881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11614617469900636125375365 2177740775606369273507881)
                      ·
                        rfl

theorem cell23_4241135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 3, 1, 4].length) (baseStart_4241135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4241135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4241135 prefixEnd_4241135 := by exact prefixLift 4241135
  have htrace : WordTrace (prefixWord ++ tailWord_4241135) baseStart_4241135 baseEnd_4241135 := by
    simpa [prefixWord, tailWord_4241135, baseEnd_4241135] using wordTrace_append hprefix tailTrace_4241135
  have hstable : (prefixWord ++ tailWord_4241135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4241135).length < 2 ^ (prefixWord ++ tailWord_4241135).sum := by decide
  have hdescent : baseEnd_4241135 < baseStart_4241135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4241135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4241192 : List Nat := [2, 1, 5, 1, 1, 4, 1, 8]
def baseStart_4241192 : Nat := 118140960795 + 4241192 * 2 ^ 59
def prefixEnd_4241192 : Nat := 4983230072969 + 3 ^ 40 * 4241192 * 2
def baseEnd_4241192 : Nat := 80658149777913909277597

theorem tailTrace_4241192 : CollatzResearch.WordTrace tailWord_4241192 prefixEnd_4241192 80658149777913909277597 := by
  unfold tailWord_4241192
  simp only [CollatzResearch.WordTrace]
  refine ⟨77344490225446598385610915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103125986967262131180814553 77344490225446598385610915)
  ·
    refine ⟨116016735338169897578416373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77344490225446598385610915 116016735338169897578416373)
    ·
      refine ⟨10876568937953427897976535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 116016735338169897578416373 10876568937953427897976535)
      ·
        refine ⟨16314853406930141846964803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10876568937953427897976535 16314853406930141846964803)
        ·
          refine ⟨24472280110395212770447205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16314853406930141846964803 24472280110395212770447205)
          ·
            refine ⟨4588552520699102394458851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24472280110395212770447205 4588552520699102394458851)
            ·
              refine ⟨6882828781048653591688277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4588552520699102394458851 6882828781048653591688277)
              ·
                refine ⟨80658149777913909277597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6882828781048653591688277 80658149777913909277597)
                ·
                  rfl

theorem cell23_4241192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 8].length) (baseStart_4241192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4241192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4241192 prefixEnd_4241192 := by exact prefixLift 4241192
  have htrace : WordTrace (prefixWord ++ tailWord_4241192) baseStart_4241192 baseEnd_4241192 := by
    simpa [prefixWord, tailWord_4241192, baseEnd_4241192] using wordTrace_append hprefix tailTrace_4241192
  have hstable : (prefixWord ++ tailWord_4241192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4241192).length < 2 ^ (prefixWord ++ tailWord_4241192).sum := by decide
  have hdescent : baseEnd_4241192 < baseStart_4241192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4241192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4241202 : List Nat := [3, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3]
def baseStart_4241202 : Nat := 118140960795 + 4241202 * 2 ^ 59
def prefixEnd_4241202 : Nat := 4983230072969 + 3 ^ 40 * 4241202 * 2
def baseEnd_4241202 : Nat := 2177775178810220511370073

theorem tailTrace_4241202 : CollatzResearch.WordTrace tailWord_4241202 prefixEnd_4241202 2177775178810220511370073 := by
  unfold tailWord_4241202
  simp only [CollatzResearch.WordTrace]
  refine ⟨38672336295214242119771465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103126230120571312319390573 38672336295214242119771465)
  ·
    refine ⟨29004252221410681589828599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38672336295214242119771465 29004252221410681589828599)
    ·
      refine ⟨43506378332116022384742899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29004252221410681589828599 43506378332116022384742899)
      ·
        refine ⟨65259567498174033577114349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43506378332116022384742899 65259567498174033577114349)
        ·
          refine ⟨24472337811815262591417881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65259567498174033577114349 24472337811815262591417881)
          ·
            refine ⟨18354253358861446943563411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24472337811815262591417881 18354253358861446943563411)
            ·
              refine ⟨27531380038292170415345117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18354253358861446943563411 27531380038292170415345117)
              ·
                refine ⟨10324267514359563905754419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27531380038292170415345117 10324267514359563905754419)
                ·
                  refine ⟨15486401271539345858631629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10324267514359563905754419 15486401271539345858631629)
                  ·
                    refine ⟨5807400476827254696986861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15486401271539345858631629 5807400476827254696986861)
                    ·
                      refine ⟨2177775178810220511370073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5807400476827254696986861 2177775178810220511370073)
                      ·
                        rfl

theorem cell23_4241202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3].length) (baseStart_4241202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4241202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4241202 prefixEnd_4241202 := by exact prefixLift 4241202
  have htrace : WordTrace (prefixWord ++ tailWord_4241202) baseStart_4241202 baseEnd_4241202 := by
    simpa [prefixWord, tailWord_4241202, baseEnd_4241202] using wordTrace_append hprefix tailTrace_4241202
  have hstable : (prefixWord ++ tailWord_4241202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4241202).length < 2 ^ (prefixWord ++ tailWord_4241202).sum := by decide
  have hdescent : baseEnd_4241202 < baseStart_4241202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4241202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4241209 : List Nat := [1, 2, 1, 7, 1, 1, 3, 7]
def baseStart_4241209 : Nat := 118140960795 + 4241209 * 2 ^ 59
def prefixEnd_4241209 : Nat := 4983230072969 + 3 ^ 40 * 4241209 * 2
def baseEnd_4241209 : Nat := 80658473080548221628983

theorem tailTrace_4241209 : CollatzResearch.WordTrace tailWord_4241209 prefixEnd_4241209 80658473080548221628983 := by
  unfold tailWord_4241209
  simp only [CollatzResearch.WordTrace]
  refine ⟨154689600491831608674590681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103126400327887739116393787 154689600491831608674590681)
  ·
    refine ⟨116017200368873706505943011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154689600491831608674590681 116017200368873706505943011)
    ·
      refine ⟨174025800553310559758914517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116017200368873706505943011 174025800553310559758914517)
      ·
        refine ⟨4078729700468216244349559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 174025800553310559758914517 4078729700468216244349559)
        ·
          refine ⟨6118094550702324366524339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4078729700468216244349559 6118094550702324366524339)
          ·
            refine ⟨9177141826053486549786509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6118094550702324366524339 9177141826053486549786509)
            ·
              refine ⟨3441428184770057456169941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9177141826053486549786509 3441428184770057456169941)
              ·
                refine ⟨80658473080548221628983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3441428184770057456169941 80658473080548221628983)
                ·
                  rfl

theorem cell23_4241209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 7].length) (baseStart_4241209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4241209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4241209 prefixEnd_4241209 := by exact prefixLift 4241209
  have htrace : WordTrace (prefixWord ++ tailWord_4241209) baseStart_4241209 baseEnd_4241209 := by
    simpa [prefixWord, tailWord_4241209, baseEnd_4241209] using wordTrace_append hprefix tailTrace_4241209
  have hstable : (prefixWord ++ tailWord_4241209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4241209).length < 2 ^ (prefixWord ++ tailWord_4241209).sum := by decide
  have hdescent : baseEnd_4241209 < baseStart_4241209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4241209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4241236 : List Nat := [2, 4, 1, 1, 3, 1, 3, 2, 2, 1, 3]
def baseStart_4241236 : Nat := 118140960795 + 4241236 * 2 ^ 59
def prefixEnd_4241236 : Nat := 4983230072969 + 3 ^ 40 * 4241236 * 2
def baseEnd_4241236 : Nat := 2177792637152473378344917

theorem tailTrace_4241236 : CollatzResearch.WordTrace tailWord_4241236 prefixEnd_4241236 2177792637152473378344917 := by
  unfold tailWord_4241236
  simp only [CollatzResearch.WordTrace]
  refine ⟨77345292631366896142911781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103127056841822528190549041 77345292631366896142911781)
  ·
    refine ⟨14502242368381293026795959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77345292631366896142911781 14502242368381293026795959)
    ·
      refine ⟨21753363552571939540193939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14502242368381293026795959 21753363552571939540193939)
      ·
        refine ⟨32630045328857909310290909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21753363552571939540193939 32630045328857909310290909)
        ·
          refine ⟨12236266998321715991359091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32630045328857909310290909 12236266998321715991359091)
          ·
            refine ⟨18354400497482573987038637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12236266998321715991359091 18354400497482573987038637)
            ·
              refine ⟨6882900186555965245139489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18354400497482573987038637 6882900186555965245139489)
              ·
                refine ⟨5162175139916973933854617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6882900186555965245139489 5162175139916973933854617)
                ·
                  refine ⟨3871631354937730450390963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5162175139916973933854617 3871631354937730450390963)
                  ·
                    refine ⟨5807447032406595675586445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3871631354937730450390963 5807447032406595675586445)
                    ·
                      refine ⟨2177792637152473378344917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5807447032406595675586445 2177792637152473378344917)
                      ·
                        rfl

theorem cell23_4241236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_4241236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4241236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4241236 prefixEnd_4241236 := by exact prefixLift 4241236
  have htrace : WordTrace (prefixWord ++ tailWord_4241236) baseStart_4241236 baseEnd_4241236 := by
    simpa [prefixWord, tailWord_4241236, baseEnd_4241236] using wordTrace_append hprefix tailTrace_4241236
  have hstable : (prefixWord ++ tailWord_4241236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4241236).length < 2 ^ (prefixWord ++ tailWord_4241236).sum := by decide
  have hdescent : baseEnd_4241236 < baseStart_4241236 := by decide
  rcases family_descends (prefixWord ++ tailWord_4241236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4241265 : List Nat := [1, 2, 2, 2, 1, 3, 1, 4, 7]
def baseStart_4241265 : Nat := 118140960795 + 4241265 * 2 ^ 59
def prefixEnd_4241265 : Nat := 4983230072969 + 3 ^ 40 * 4241265 * 2
def baseEnd_4241265 : Nat := 241978614232383751653587

theorem tailTrace_4241265 : CollatzResearch.WordTrace tailWord_4241265 prefixEnd_4241265 241978614232383751653587 := by
  unfold tailWord_4241265
  simp only [CollatzResearch.WordTrace]
  refine ⟨154691642979628730238629249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103127761986419153492419499 154691642979628730238629249)
  ·
    refine ⟨116018732234721547678971937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154691642979628730238629249 116018732234721547678971937)
    ·
      refine ⟨87014049176041160759228953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116018732234721547678971937 87014049176041160759228953)
      ·
        refine ⟨65260536882030870569421715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87014049176041160759228953 65260536882030870569421715)
        ·
          refine ⟨97890805323046305854132573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65260536882030870569421715 97890805323046305854132573)
          ·
            refine ⟨36709051996142364695299715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97890805323046305854132573 36709051996142364695299715)
            ·
              refine ⟨55063577994213547042949573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36709051996142364695299715 55063577994213547042949573)
              ·
                refine ⟨10324420873915040070553045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55063577994213547042949573 10324420873915040070553045)
                ·
                  refine ⟨241978614232383751653587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10324420873915040070553045 241978614232383751653587)
                  ·
                    rfl

theorem cell23_4241265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 7].length) (baseStart_4241265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4241265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4241265 prefixEnd_4241265 := by exact prefixLift 4241265
  have htrace : WordTrace (prefixWord ++ tailWord_4241265) baseStart_4241265 baseEnd_4241265 := by
    simpa [prefixWord, tailWord_4241265, baseEnd_4241265] using wordTrace_append hprefix tailTrace_4241265
  have hstable : (prefixWord ++ tailWord_4241265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4241265).length < 2 ^ (prefixWord ++ tailWord_4241265).sum := by decide
  have hdescent : baseEnd_4241265 < baseStart_4241265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4241265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4241305 : List Nat := [1, 2, 1, 2, 1, 3, 3, 1, 1, 1, 7]
def baseStart_4241305 : Nat := 118140960795 + 4241305 * 2 ^ 59
def prefixEnd_4241305 : Nat := 4983230072969 + 3 ^ 40 * 4241305 * 2
def baseEnd_4241305 : Nat := 2177828067317633608382099

theorem tailTrace_4241305 : CollatzResearch.WordTrace tailWord_4241305 prefixEnd_4241305 2177828067317633608382099 := by
  unfold tailWord_4241305
  simp only [CollatzResearch.WordTrace]
  refine ⟨154693101899483817070085369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103128734599655878046723579 154693101899483817070085369)
  ·
    refine ⟨116019826424612862802564027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154693101899483817070085369 116019826424612862802564027)
    ·
      refine ⟨174029739636919294203846041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116019826424612862802564027 174029739636919294203846041)
      ·
        refine ⟨130522304727689470652884531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174029739636919294203846041 130522304727689470652884531)
        ·
          refine ⟨195783457091534205979326797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130522304727689470652884531 195783457091534205979326797)
          ·
            refine ⟨73418796409325327242247549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 195783457091534205979326797 73418796409325327242247549)
            ·
              refine ⟨27532048653496997715842831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73418796409325327242247549 27532048653496997715842831)
              ·
                refine ⟨41298072980245496573764247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27532048653496997715842831 41298072980245496573764247)
                ·
                  refine ⟨61947109470368244860646371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41298072980245496573764247 61947109470368244860646371)
                  ·
                    refine ⟨92920664205552367290969557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61947109470368244860646371 92920664205552367290969557)
                    ·
                      refine ⟨2177828067317633608382099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 92920664205552367290969557 2177828067317633608382099)
                      ·
                        rfl

theorem cell23_4241305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 1, 7].length) (baseStart_4241305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4241305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4241305 prefixEnd_4241305 := by exact prefixLift 4241305
  have htrace : WordTrace (prefixWord ++ tailWord_4241305) baseStart_4241305 baseEnd_4241305 := by
    simpa [prefixWord, tailWord_4241305, baseEnd_4241305] using wordTrace_append hprefix tailTrace_4241305
  have hstable : (prefixWord ++ tailWord_4241305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4241305).length < 2 ^ (prefixWord ++ tailWord_4241305).sum := by decide
  have hdescent : baseEnd_4241305 < baseStart_4241305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4241305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4241329 : List Nat := [1, 2, 2, 4, 2, 2, 2, 1, 2, 5]
def baseStart_4241329 : Nat := 118140960795 + 4241329 * 2 ^ 59
def prefixEnd_4241329 : Nat := 4983230072969 + 3 ^ 40 * 4241329 * 2
def baseEnd_4241329 : Nat := 725946796951113838160663

theorem tailTrace_4241329 : CollatzResearch.WordTrace tailWord_4241329 prefixEnd_4241329 725946796951113838160663 := by
  unfold tailWord_4241329
  simp only [CollatzResearch.WordTrace]
  refine ⟨154693977251396869168959041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103129318167597912779306027 154693977251396869168959041)
  ·
    refine ⟨116020482938547651876719281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154693977251396869168959041 116020482938547651876719281)
    ·
      refine ⟨87015362203910738907539461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116020482938547651876719281 87015362203910738907539461)
      ·
        refine ⟨16315380413233263545163649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87015362203910738907539461 16315380413233263545163649)
        ·
          refine ⟨12236535309924947658872737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16315380413233263545163649 12236535309924947658872737)
          ·
            refine ⟨9177401482443710744154553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12236535309924947658872737 9177401482443710744154553)
            ·
              refine ⟨6883051111832783058115915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9177401482443710744154553 6883051111832783058115915)
              ·
                refine ⟨10324576667749174587173873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6883051111832783058115915 10324576667749174587173873)
                ·
                  refine ⟨7743432500811880940380405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10324576667749174587173873 7743432500811880940380405)
                  ·
                    refine ⟨725946796951113838160663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7743432500811880940380405 725946796951113838160663)
                    ·
                      rfl

theorem cell23_4241329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 2, 5].length) (baseStart_4241329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4241329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4241329 prefixEnd_4241329 := by exact prefixLift 4241329
  have htrace : WordTrace (prefixWord ++ tailWord_4241329) baseStart_4241329 baseEnd_4241329 := by
    simpa [prefixWord, tailWord_4241329, baseEnd_4241329] using wordTrace_append hprefix tailTrace_4241329
  have hstable : (prefixWord ++ tailWord_4241329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4241329).length < 2 ^ (prefixWord ++ tailWord_4241329).sum := by decide
  have hdescent : baseEnd_4241329 < baseStart_4241329 := by decide
  rcases family_descends (prefixWord ++ tailWord_4241329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4241383 : List Nat := [1, 1, 5, 2, 4, 1, 1, 1, 2, 1, 4]
def baseStart_4241383 : Nat := 118140960795 + 4241383 * 2 ^ 59
def prefixEnd_4241383 : Nat := 4983230072969 + 3 ^ 40 * 4241383 * 2
def baseEnd_4241383 : Nat := 2177868118808684303206741

theorem tailTrace_4241383 : CollatzResearch.WordTrace tailWord_4241383 prefixEnd_4241383 2177868118808684303206741 := by
  unfold tailWord_4241383
  simp only [CollatzResearch.WordTrace]
  refine ⟨154695946793201236391424803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103130631195467490927616535 154695946793201236391424803)
  ·
    refine ⟨232043920189801854587137205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154695946793201236391424803 232043920189801854587137205)
    ·
      refine ⟨21754117517793923867544113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 232043920189801854587137205 21754117517793923867544113)
      ·
        refine ⟨16315588138345442900658085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21754117517793923867544113 16315588138345442900658085)
        ·
          refine ⟨3059172775939770543873391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16315588138345442900658085 3059172775939770543873391)
          ·
            refine ⟨4588759163909655815810087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3059172775939770543873391 4588759163909655815810087)
            ·
              refine ⟨6883138745864483723715131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4588759163909655815810087 6883138745864483723715131)
              ·
                refine ⟨10324708118796725585572697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6883138745864483723715131 10324708118796725585572697)
                ·
                  refine ⟨7743531089097544189179523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10324708118796725585572697 7743531089097544189179523)
                  ·
                    refine ⟨11615296633646316283769285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7743531089097544189179523 11615296633646316283769285)
                    ·
                      refine ⟨2177868118808684303206741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11615296633646316283769285 2177868118808684303206741)
                      ·
                        rfl

theorem cell23_4241383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_4241383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4241383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4241383 prefixEnd_4241383 := by exact prefixLift 4241383
  have htrace : WordTrace (prefixWord ++ tailWord_4241383) baseStart_4241383 baseEnd_4241383 := by
    simpa [prefixWord, tailWord_4241383, baseEnd_4241383] using wordTrace_append hprefix tailTrace_4241383
  have hstable : (prefixWord ++ tailWord_4241383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4241383).length < 2 ^ (prefixWord ++ tailWord_4241383).sum := by decide
  have hdescent : baseEnd_4241383 < baseStart_4241383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4241383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4241393 : List Nat := [1, 2, 2, 2, 5, 1, 2, 3, 1, 4]
def baseStart_4241393 : Nat := 118140960795 + 4241393 * 2 ^ 59
def prefixEnd_4241393 : Nat := 4983230072969 + 3 ^ 40 * 4241393 * 2
def baseEnd_4241393 : Nat := 725957751205076421360565

theorem tailTrace_4241393 : CollatzResearch.WordTrace tailWord_4241393 prefixEnd_4241393 725957751205076421360565 := by
  unfold tailWord_4241393
  simp only [CollatzResearch.WordTrace]
  refine ⟨154696311523165008099288833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103130874348776672066192555 154696311523165008099288833)
  ·
    refine ⟨116022233642373756074466625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154696311523165008099288833 116022233642373756074466625)
    ·
      refine ⟨87016675231780317055849969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116022233642373756074466625 87016675231780317055849969)
      ·
        refine ⟨65262506423835237791887477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87016675231780317055849969 65262506423835237791887477)
        ·
          refine ⟨6118359977234553542989451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65262506423835237791887477 6118359977234553542989451)
          ·
            refine ⟨9177539965851830314484177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6118359977234553542989451 9177539965851830314484177)
            ·
              refine ⟨6883154974388872735863133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9177539965851830314484177 6883154974388872735863133)
              ·
                refine ⟨2581183115395827275948675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6883154974388872735863133 2581183115395827275948675)
                ·
                  refine ⟨3871774673093740913923013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2581183115395827275948675 3871774673093740913923013)
                  ·
                    refine ⟨725957751205076421360565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3871774673093740913923013 725957751205076421360565)
                    ·
                      rfl

theorem cell23_4241393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 3, 1, 4].length) (baseStart_4241393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4241393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4241393 prefixEnd_4241393 := by exact prefixLift 4241393
  have htrace : WordTrace (prefixWord ++ tailWord_4241393) baseStart_4241393 baseEnd_4241393 := by
    simpa [prefixWord, tailWord_4241393, baseEnd_4241393] using wordTrace_append hprefix tailTrace_4241393
  have hstable : (prefixWord ++ tailWord_4241393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4241393).length < 2 ^ (prefixWord ++ tailWord_4241393).sum := by decide
  have hdescent : baseEnd_4241393 < baseStart_4241393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4241393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4241406 : List Nat := [4, 2, 2, 2, 1, 1, 3, 2, 6]
def baseStart_4241406 : Nat := 118140960795 + 4241406 * 2 ^ 59
def prefixEnd_4241406 : Nat := 4983230072969 + 3 ^ 40 * 4241406 * 2
def baseEnd_4241406 : Nat := 241986658762637523691015

theorem tailTrace_4241406 : CollatzResearch.WordTrace tailWord_4241406 prefixEnd_4241406 241986658762637523691015 := by
  unfold tailWord_4241406
  simp only [CollatzResearch.WordTrace]
  refine ⟨19337098209014738914939009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103131190448078607546341381 19337098209014738914939009)
  ·
    refine ⟨14502823656761054186204257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19337098209014738914939009 14502823656761054186204257)
    ·
      refine ⟨10877117742570790639653193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14502823656761054186204257 10877117742570790639653193)
      ·
        refine ⟨8157838306928092979739895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10877117742570790639653193 8157838306928092979739895)
        ·
          refine ⟨12236757460392139469609843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8157838306928092979739895 12236757460392139469609843)
          ·
            refine ⟨18355136190588209204414765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12236757460392139469609843 18355136190588209204414765)
            ·
              refine ⟨6883176071470578451655537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18355136190588209204414765 6883176071470578451655537)
              ·
                refine ⟨5162382053602933838741653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6883176071470578451655537 5162382053602933838741653)
                ·
                  refine ⟨241986658762637523691015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5162382053602933838741653 241986658762637523691015)
                  ·
                    rfl

theorem cell23_4241406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_4241406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4241406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4241406 prefixEnd_4241406 := by exact prefixLift 4241406
  have htrace : WordTrace (prefixWord ++ tailWord_4241406) baseStart_4241406 baseEnd_4241406 := by
    simpa [prefixWord, tailWord_4241406, baseEnd_4241406] using wordTrace_append hprefix tailTrace_4241406
  have hstable : (prefixWord ++ tailWord_4241406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4241406).length < 2 ^ (prefixWord ++ tailWord_4241406).sum := by decide
  have hdescent : baseEnd_4241406 < baseStart_4241406 := by decide
  rcases family_descends (prefixWord ++ tailWord_4241406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4241416 : List Nat := [2, 1, 3, 2, 1, 2, 4, 1, 3, 1, 3]
def baseStart_4241416 : Nat := 118140960795 + 4241416 * 2 ^ 59
def prefixEnd_4241416 : Nat := 4983230072969 + 3 ^ 40 * 4241416 * 2
def baseEnd_4241416 : Nat := 2177885063670282674094089

theorem tailTrace_4241416 : CollatzResearch.WordTrace tailWord_4241416 prefixEnd_4241416 2177885063670282674094089 := by
  unfold tailWord_4241416
  simp only [CollatzResearch.WordTrace]
  refine ⟨77348575201040841513688051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103131433601387788684917401 77348575201040841513688051)
  ·
    refine ⟨116022862801561262270532077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77348575201040841513688051 116022862801561262270532077)
    ·
      refine ⟨43508573550585473351449529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116022862801561262270532077 43508573550585473351449529)
      ·
        refine ⟨32631430162939105013587147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43508573550585473351449529 32631430162939105013587147)
        ·
          refine ⟨48947145244408657520380721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32631430162939105013587147 48947145244408657520380721)
          ·
            refine ⟨36710358933306493140285541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48947145244408657520380721 36710358933306493140285541)
            ·
              refine ⟨6883192299994967463803539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36710358933306493140285541 6883192299994967463803539)
              ·
                refine ⟨10324788449992451195705309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6883192299994967463803539 10324788449992451195705309)
                ·
                  refine ⟨3871795668747169198389491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10324788449992451195705309 3871795668747169198389491)
                  ·
                    refine ⟨5807693503120753797584237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3871795668747169198389491 5807693503120753797584237)
                    ·
                      refine ⟨2177885063670282674094089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5807693503120753797584237 2177885063670282674094089)
                      ·
                        rfl

theorem cell23_4241416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_4241416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4241416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4241416 prefixEnd_4241416 := by exact prefixLift 4241416
  have htrace : WordTrace (prefixWord ++ tailWord_4241416) baseStart_4241416 baseEnd_4241416 := by
    simpa [prefixWord, tailWord_4241416, baseEnd_4241416] using wordTrace_append hprefix tailTrace_4241416
  have hstable : (prefixWord ++ tailWord_4241416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4241416).length < 2 ^ (prefixWord ++ tailWord_4241416).sum := by decide
  have hdescent : baseEnd_4241416 < baseStart_4241416 := by decide
  rcases family_descends (prefixWord ++ tailWord_4241416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4241436 : List Nat := [2, 2, 3, 1, 3, 2, 2, 2, 1, 5]
def baseStart_4241436 : Nat := 118140960795 + 4241436 * 2 ^ 59
def prefixEnd_4241436 : Nat := 4983230072969 + 3 ^ 40 * 4241436 * 2
def baseEnd_4241436 : Nat := 725965111094457531947999

theorem tailTrace_4241436 : CollatzResearch.WordTrace tailWord_4241436 prefixEnd_4241436 725965111094457531947999 := by
  unfold tailWord_4241436
  simp only [CollatzResearch.WordTrace]
  refine ⟨77348939931004613221552081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103131919908006150962069441 77348939931004613221552081)
  ·
    refine ⟨58011704948253459916164061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77348939931004613221552081 58011704948253459916164061)
    ·
      refine ⟨21754389355595047468561523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58011704948253459916164061 21754389355595047468561523)
      ·
        refine ⟨32631584033392571202842285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21754389355595047468561523 32631584033392571202842285)
        ·
          refine ⟨12236844012522214201065857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32631584033392571202842285 12236844012522214201065857)
          ·
            refine ⟨9177633009391660650799393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12236844012522214201065857 9177633009391660650799393)
            ·
              refine ⟨6883224757043745488099545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9177633009391660650799393 6883224757043745488099545)
              ·
                refine ⟨5162418567782809116074659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6883224757043745488099545 5162418567782809116074659)
                ·
                  refine ⟨7743627851674213674111989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5162418567782809116074659 7743627851674213674111989)
                  ·
                    refine ⟨725965111094457531947999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7743627851674213674111989 725965111094457531947999)
                    ·
                      rfl

theorem cell23_4241436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_4241436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4241436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4241436 prefixEnd_4241436 := by exact prefixLift 4241436
  have htrace : WordTrace (prefixWord ++ tailWord_4241436) baseStart_4241436 baseEnd_4241436 := by
    simpa [prefixWord, tailWord_4241436, baseEnd_4241436] using wordTrace_append hprefix tailTrace_4241436
  have hstable : (prefixWord ++ tailWord_4241436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4241436).length < 2 ^ (prefixWord ++ tailWord_4241436).sum := by decide
  have hdescent : baseEnd_4241436 < baseStart_4241436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4241436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4241439 : List Nat := [1, 1, 2, 4, 1, 2, 1, 1, 2, 6, 2]
def baseStart_4241439 : Nat := 118140960795 + 4241439 * 2 ^ 59
def prefixEnd_4241439 : Nat := 4983230072969 + 3 ^ 40 * 4241439 * 2
def baseEnd_4241439 : Nat := 2177896873725336084106483

theorem tailTrace_4241439 : CollatzResearch.WordTrace tailWord_4241439 prefixEnd_4241439 2177896873725336084106483 := by
  unfold tailWord_4241439
  simp only [CollatzResearch.WordTrace]
  refine ⟨154697989280998357955463371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103131992853998905303642247 154697989280998357955463371)
  ·
    refine ⟨232046983921497536933195057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154697989280998357955463371 232046983921497536933195057)
    ·
      refine ⟨174035237941123152699896293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232046983921497536933195057 174035237941123152699896293)
      ·
        refine ⟨32631607113960591131230555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 174035237941123152699896293 32631607113960591131230555)
        ·
          refine ⟨48947410670940886696845833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32631607113960591131230555 48947410670940886696845833)
          ·
            refine ⟨36710558003205665022634375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48947410670940886696845833 36710558003205665022634375)
            ·
              refine ⟨55065837004808497533951563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36710558003205665022634375 55065837004808497533951563)
              ·
                refine ⟨82598755507212746300927345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55065837004808497533951563 82598755507212746300927345)
                ·
                  refine ⟨61949066630409559725695509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82598755507212746300927345 61949066630409559725695509)
                  ·
                    refine ⟨2903862498300448112141977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 61949066630409559725695509 2903862498300448112141977)
                    ·
                      refine ⟨2177896873725336084106483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2903862498300448112141977 2177896873725336084106483)
                      ·
                        rfl

theorem cell23_4241439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 6, 2].length) (baseStart_4241439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4241439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4241439 prefixEnd_4241439 := by exact prefixLift 4241439
  have htrace : WordTrace (prefixWord ++ tailWord_4241439) baseStart_4241439 baseEnd_4241439 := by
    simpa [prefixWord, tailWord_4241439, baseEnd_4241439] using wordTrace_append hprefix tailTrace_4241439
  have hstable : (prefixWord ++ tailWord_4241439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4241439).length < 2 ^ (prefixWord ++ tailWord_4241439).sum := by decide
  have hdescent : baseEnd_4241439 < baseStart_4241439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4241439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4241450 : List Nat := [3, 1, 4, 1, 2, 1, 3, 3, 1, 1, 3]
def baseStart_4241450 : Nat := 118140960795 + 4241450 * 2 ^ 59
def prefixEnd_4241450 : Nat := 4983230072969 + 3 ^ 40 * 4241450 * 2
def baseEnd_4241450 : Nat := 2177902522012535541068933

theorem tailTrace_4241450 : CollatzResearch.WordTrace tailWord_4241450 prefixEnd_4241450 2177902522012535541068933 := by
  unfold tailWord_4241450
  simp only [CollatzResearch.WordTrace]
  refine ⟨38674597620989626708528451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103132260322639004556075869 38674597620989626708528451)
  ·
    refine ⟨58011896431484440062792677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38674597620989626708528451 58011896431484440062792677)
    ·
      refine ⟨10877230580903332511773627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58011896431484440062792677 10877230580903332511773627)
      ·
        refine ⟨16315845871354998767660441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10877230580903332511773627 16315845871354998767660441)
        ·
          refine ⟨12236884403516249075745331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16315845871354998767660441 12236884403516249075745331)
          ·
            refine ⟨18355326605274373613617997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12236884403516249075745331 18355326605274373613617997)
            ·
              refine ⟨6883247476977890105106749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18355326605274373613617997 6883247476977890105106749)
              ·
                refine ⟨2581217803866708789415031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6883247476977890105106749 2581217803866708789415031)
                ·
                  refine ⟨3871826705800063184122547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2581217803866708789415031 3871826705800063184122547)
                  ·
                    refine ⟨5807740058700094776183821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3871826705800063184122547 5807740058700094776183821)
                    ·
                      refine ⟨2177902522012535541068933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5807740058700094776183821 2177902522012535541068933)
                      ·
                        rfl

theorem cell23_4241450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_4241450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4241450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4241450 prefixEnd_4241450 := by exact prefixLift 4241450
  have htrace : WordTrace (prefixWord ++ tailWord_4241450) baseStart_4241450 baseEnd_4241450 := by
    simpa [prefixWord, tailWord_4241450, baseEnd_4241450] using wordTrace_append hprefix tailTrace_4241450
  have hstable : (prefixWord ++ tailWord_4241450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4241450).length < 2 ^ (prefixWord ++ tailWord_4241450).sum := by decide
  have hdescent : baseEnd_4241450 < baseStart_4241450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4241450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4241460 : List Nat := [2, 5, 1, 2, 2, 1, 1, 2, 2, 3, 2]
def baseStart_4241460 : Nat := 118140960795 + 4241460 * 2 ^ 59
def prefixEnd_4241460 : Nat := 4983230072969 + 3 ^ 40 * 4241460 * 2
def baseEnd_4241460 : Nat := 2177907656819080501943887

theorem tailTrace_4241460 : CollatzResearch.WordTrace tailWord_4241460 prefixEnd_4241460 2177907656819080501943887 := by
  unfold tailWord_4241460
  simp only [CollatzResearch.WordTrace]
  refine ⟨77349377606961139270988917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103132503475948185694651889 77349377606961139270988917)
  ·
    refine ⟨7251504150652606806655211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77349377606961139270988917 7251504150652606806655211)
    ·
      refine ⟨10877256225978910209982817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7251504150652606806655211 10877256225978910209982817)
      ·
        refine ⟨8157942169484182657487113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10877256225978910209982817 8157942169484182657487113)
        ·
          refine ⟨6118456627113136993115335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8157942169484182657487113 6118456627113136993115335)
          ·
            refine ⟨9177684940669705489673003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6118456627113136993115335 9177684940669705489673003)
            ·
              refine ⟨13766527411004558234509505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9177684940669705489673003 13766527411004558234509505)
              ·
                refine ⟨10324895558253418675882129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13766527411004558234509505 10324895558253418675882129)
                ·
                  refine ⟨7743671668690064006911597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10324895558253418675882129 7743671668690064006911597)
                  ·
                    refine ⟨2903876875758774002591849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7743671668690064006911597 2903876875758774002591849)
                    ·
                      refine ⟨2177907656819080501943887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2903876875758774002591849 2177907656819080501943887)
                      ·
                        rfl

theorem cell23_4241460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_4241460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4241460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4241460 prefixEnd_4241460 := by exact prefixLift 4241460
  have htrace : WordTrace (prefixWord ++ tailWord_4241460) baseStart_4241460 baseEnd_4241460 := by
    simpa [prefixWord, tailWord_4241460, baseEnd_4241460] using wordTrace_append hprefix tailTrace_4241460
  have hstable : (prefixWord ++ tailWord_4241460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4241460).length < 2 ^ (prefixWord ++ tailWord_4241460).sum := by decide
  have hdescent : baseEnd_4241460 < baseStart_4241460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4241460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4241482 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 1, 4, 6]
def baseStart_4241482 : Nat := 118140960795 + 4241482 * 2 ^ 59
def prefixEnd_4241482 : Nat := 4983230072969 + 3 ^ 40 * 4241482 * 2
def baseEnd_4241482 : Nat := 2177918953393479415868785

theorem tailTrace_4241482 : CollatzResearch.WordTrace tailWord_4241482 prefixEnd_4241482 2177918953393479415868785 := by
  unfold tailWord_4241482
  simp only [CollatzResearch.WordTrace]
  refine ⟨38674889404960644074819675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103133038413228384199519133 38674889404960644074819675)
  ·
    refine ⟨58012334107440966112229513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38674889404960644074819675 58012334107440966112229513)
    ·
      refine ⟨43509250580580724584172135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58012334107440966112229513 43509250580580724584172135)
      ·
        refine ⟨65263875870871086876258203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43509250580580724584172135 65263875870871086876258203)
        ·
          refine ⟨97895813806306630314387305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65263875870871086876258203 97895813806306630314387305)
          ·
            refine ⟨73421860354729972735790479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97895813806306630314387305 73421860354729972735790479)
            ·
              refine ⟨110132790532094959103685719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73421860354729972735790479 110132790532094959103685719)
              ·
                refine ⟨165199185798142438655528579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110132790532094959103685719 165199185798142438655528579)
                ·
                  refine ⟨247798778697213657983292869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 165199185798142438655528579 247798778697213657983292869)
                  ·
                    refine ⟨46462271005727560871867413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 247798778697213657983292869 46462271005727560871867413)
                    ·
                      refine ⟨2177918953393479415868785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46462271005727560871867413 2177918953393479415868785)
                      ·
                        rfl

theorem cell23_4241482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_4241482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4241482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4241482 prefixEnd_4241482 := by exact prefixLift 4241482
  have htrace : WordTrace (prefixWord ++ tailWord_4241482) baseStart_4241482 baseEnd_4241482 := by
    simpa [prefixWord, tailWord_4241482, baseEnd_4241482] using wordTrace_append hprefix tailTrace_4241482
  have hstable : (prefixWord ++ tailWord_4241482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4241482).length < 2 ^ (prefixWord ++ tailWord_4241482).sum := by decide
  have hdescent : baseEnd_4241482 < baseStart_4241482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4241482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4241489 : List Nat := [1, 2, 2, 1, 3, 1, 1, 5, 1, 3, 3]
def baseStart_4241489 : Nat := 118140960795 + 4241489 * 2 ^ 59
def prefixEnd_4241489 : Nat := 4983230072969 + 3 ^ 40 * 4241489 * 2
def baseEnd_4241489 : Nat := 2177922547758060888481253

theorem tailTrace_4241489 : CollatzResearch.WordTrace tailWord_4241489 prefixEnd_4241489 2177922547758060888481253 := by
  unfold tailWord_4241489
  simp only [CollatzResearch.WordTrace]
  refine ⟨154699812930817216494783521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103133208620544810996522347 154699812930817216494783521)
  ·
    refine ⟨116024859698112912371087641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154699812930817216494783521 116024859698112912371087641)
    ·
      refine ⟨87018644773584684278315731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116024859698112912371087641 87018644773584684278315731)
      ·
        refine ⟨130527967160377026417473597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87018644773584684278315731 130527967160377026417473597)
        ·
          refine ⟨48947987685141384906552599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130527967160377026417473597 48947987685141384906552599)
          ·
            refine ⟨73421981527712077359828899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48947987685141384906552599 73421981527712077359828899)
            ·
              refine ⟨110132972291568116039743349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73421981527712077359828899 110132972291568116039743349)
              ·
                refine ⟨10324966152334510878725939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 110132972291568116039743349 10324966152334510878725939)
                ·
                  refine ⟨15487449228501766318088909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10324966152334510878725939 15487449228501766318088909)
                  ·
                    refine ⟨5807793460688162369283341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15487449228501766318088909 5807793460688162369283341)
                    ·
                      refine ⟨2177922547758060888481253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5807793460688162369283341 2177922547758060888481253)
                      ·
                        rfl

theorem cell23_4241489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 3, 3].length) (baseStart_4241489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4241489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4241489 prefixEnd_4241489 := by exact prefixLift 4241489
  have htrace : WordTrace (prefixWord ++ tailWord_4241489) baseStart_4241489 baseEnd_4241489 := by
    simpa [prefixWord, tailWord_4241489, baseEnd_4241489] using wordTrace_append hprefix tailTrace_4241489
  have hstable : (prefixWord ++ tailWord_4241489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4241489).length < 2 ^ (prefixWord ++ tailWord_4241489).sum := by decide
  have hdescent : baseEnd_4241489 < baseStart_4241489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4241489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4241490 : List Nat := [3, 2, 2, 1, 5, 1, 1, 2, 1, 1, 4]
def baseStart_4241490 : Nat := 118140960795 + 4241490 * 2 ^ 59
def prefixEnd_4241490 : Nat := 4983230072969 + 3 ^ 40 * 4241490 * 2
def baseEnd_4241490 : Nat := 2177923061238715384568749

theorem tailTrace_4241490 : CollatzResearch.WordTrace tailWord_4241490 prefixEnd_4241490 2177923061238715384568749 := by
  unfold tailWord_4241490
  simp only [CollatzResearch.WordTrace]
  refine ⟨38674962350953398416392481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103133232935875729110379949 38674962350953398416392481)
  ·
    refine ⟨29006221763215048812294361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38674962350953398416392481 29006221763215048812294361)
    ·
      refine ⟨21754666322411286609220771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29006221763215048812294361 21754666322411286609220771)
      ·
        refine ⟨32631999483616929913831157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21754666322411286609220771 32631999483616929913831157)
        ·
          refine ⟨3059249951589087179421671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32631999483616929913831157 3059249951589087179421671)
          ·
            refine ⟨4588874927383630769132507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3059249951589087179421671 4588874927383630769132507)
            ·
              refine ⟨6883312391075446153698761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4588874927383630769132507 6883312391075446153698761)
              ·
                refine ⟨5162484293306584615274071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6883312391075446153698761 5162484293306584615274071)
                ·
                  refine ⟨7743726439959876922911107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5162484293306584615274071 7743726439959876922911107)
                  ·
                    refine ⟨11615589659939815384366661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7743726439959876922911107 11615589659939815384366661)
                    ·
                      refine ⟨2177923061238715384568749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11615589659939815384366661 2177923061238715384568749)
                      ·
                        rfl

theorem cell23_4241490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 2, 1, 1, 4].length) (baseStart_4241490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4241490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4241490 prefixEnd_4241490 := by exact prefixLift 4241490
  have htrace : WordTrace (prefixWord ++ tailWord_4241490) baseStart_4241490 baseEnd_4241490 := by
    simpa [prefixWord, tailWord_4241490, baseEnd_4241490] using wordTrace_append hprefix tailTrace_4241490
  have hstable : (prefixWord ++ tailWord_4241490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4241490).length < 2 ^ (prefixWord ++ tailWord_4241490).sum := by decide
  have hdescent : baseEnd_4241490 < baseStart_4241490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4241490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4241493 : List Nat := [1, 3, 2, 2, 1, 5, 1, 2, 1, 2, 3]
def baseStart_4241493 : Nat := 118140960795 + 4241493 * 2 ^ 59
def prefixEnd_4241493 : Nat := 4983230072969 + 3 ^ 40 * 4241493 * 2
def baseEnd_4241493 : Nat := 2177924601680678872831235

theorem tailTrace_4241493 : CollatzResearch.WordTrace tailWord_4241493 prefixEnd_4241493 2177924601680678872831235 := by
  unfold tailWord_4241493
  simp only [CollatzResearch.WordTrace]
  refine ⟨154699958822802725177929133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103133305881868483451952755 154699958822802725177929133)
  ·
    refine ⟨58012484558551021941723425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154699958822802725177929133 58012484558551021941723425)
    ·
      refine ⟨43509363418913266456292569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58012484558551021941723425 43509363418913266456292569)
      ·
        refine ⟨32632022564184949842219427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43509363418913266456292569 32632022564184949842219427)
        ·
          refine ⟨48948033846277424763329141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32632022564184949842219427 48948033846277424763329141)
          ·
            refine ⟨4588878173088508571562107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48948033846277424763329141 4588878173088508571562107)
            ·
              refine ⟨6883317259632762857343161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4588878173088508571562107 6883317259632762857343161)
              ·
                refine ⟨5162487944724572143007371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6883317259632762857343161 5162487944724572143007371)
                ·
                  refine ⟨7743731917086858214511057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5162487944724572143007371 7743731917086858214511057)
                  ·
                    refine ⟨5807798937815143660883293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7743731917086858214511057 5807798937815143660883293)
                    ·
                      refine ⟨2177924601680678872831235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5807798937815143660883293 2177924601680678872831235)
                      ·
                        rfl

theorem cell23_4241493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_4241493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4241493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4241493 prefixEnd_4241493 := by exact prefixLift 4241493
  have htrace : WordTrace (prefixWord ++ tailWord_4241493) baseStart_4241493 baseEnd_4241493 := by
    simpa [prefixWord, tailWord_4241493, baseEnd_4241493] using wordTrace_append hprefix tailTrace_4241493
  have hstable : (prefixWord ++ tailWord_4241493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4241493).length < 2 ^ (prefixWord ++ tailWord_4241493).sum := by decide
  have hdescent : baseEnd_4241493 < baseStart_4241493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4241493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4241529 : List Nat := [1, 2, 1, 3, 4, 1, 1, 1, 2, 3, 4]
def baseStart_4241529 : Nat := 118140960795 + 4241529 * 2 ^ 59
def prefixEnd_4241529 : Nat := 4983230072969 + 3 ^ 40 * 4241529 * 2
def baseEnd_4241529 : Nat := 2177943086984240731981069

theorem tailTrace_4241529 : CollatzResearch.WordTrace tailWord_4241529 prefixEnd_4241529 2177943086984240731981069 := by
  unfold tailWord_4241529
  simp only [CollatzResearch.WordTrace]
  refine ⟨154701271850672303326239641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103134181233781535550826427 154701271850672303326239641)
  ·
    refine ⟨116025953888004227494679731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154701271850672303326239641 116025953888004227494679731)
    ·
      refine ⟨174038930832006341242019597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116025953888004227494679731 174038930832006341242019597)
      ·
        refine ⟨65264599062002377965757349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 174038930832006341242019597 65264599062002377965757349)
        ·
          refine ⟨12237112324125445868579503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65264599062002377965757349 12237112324125445868579503)
          ·
            refine ⟨18355668486188168802869255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12237112324125445868579503 18355668486188168802869255)
            ·
              refine ⟨27533502729282253204303883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18355668486188168802869255 27533502729282253204303883)
              ·
                refine ⟨41300254093923379806455825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27533502729282253204303883 41300254093923379806455825)
                ·
                  refine ⟨30975190570442534854841869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41300254093923379806455825 30975190570442534854841869)
                  ·
                    refine ⟨11615696463915950570565701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30975190570442534854841869 11615696463915950570565701)
                    ·
                      refine ⟨2177943086984240731981069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11615696463915950570565701 2177943086984240731981069)
                      ·
                        rfl

theorem cell23_4241529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_4241529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4241529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4241529 prefixEnd_4241529 := by exact prefixLift 4241529
  have htrace : WordTrace (prefixWord ++ tailWord_4241529) baseStart_4241529 baseEnd_4241529 := by
    simpa [prefixWord, tailWord_4241529, baseEnd_4241529] using wordTrace_append hprefix tailTrace_4241529
  have hstable : (prefixWord ++ tailWord_4241529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4241529).length < 2 ^ (prefixWord ++ tailWord_4241529).sum := by decide
  have hdescent : baseEnd_4241529 < baseStart_4241529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4241529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4241539 : List Nat := [1, 1, 1, 3, 3, 4, 1, 1, 2, 6]
def baseStart_4241539 : Nat := 118140960795 + 4241539 * 2 ^ 59
def prefixEnd_4241539 : Nat := 4983230072969 + 3 ^ 40 * 4241539 * 2
def baseEnd_4241539 : Nat := 725982740596928564285341

theorem tailTrace_4241539 : CollatzResearch.WordTrace tailWord_4241539 prefixEnd_4241539 725982740596928564285341 := by
  unfold tailWord_4241539
  simp only [CollatzResearch.WordTrace]
  refine ⟨154701636580636075034103671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103134424387090716689402447 154701636580636075034103671)
  ·
    refine ⟨232052454870954112551155507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154701636580636075034103671 232052454870954112551155507)
    ·
      refine ⟨348078682306431168826733261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232052454870954112551155507 348078682306431168826733261)
      ·
        refine ⟨130529505864911688310024973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 348078682306431168826733261 130529505864911688310024973)
        ·
          refine ⟨48948564699341883116259365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130529505864911688310024973 48948564699341883116259365)
          ·
            refine ⟨9177855881126603084298631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48948564699341883116259365 9177855881126603084298631)
            ·
              refine ⟨13766783821689904626447947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9177855881126603084298631 13766783821689904626447947)
              ·
                refine ⟨20650175732534856939671921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13766783821689904626447947 20650175732534856939671921)
                ·
                  refine ⟨15487631799401142704753941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20650175732534856939671921 15487631799401142704753941)
                  ·
                    refine ⟨725982740596928564285341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15487631799401142704753941 725982740596928564285341)
                    ·
                      rfl

theorem cell23_4241539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 6].length) (baseStart_4241539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4241539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4241539 prefixEnd_4241539 := by exact prefixLift 4241539
  have htrace : WordTrace (prefixWord ++ tailWord_4241539) baseStart_4241539 baseEnd_4241539 := by
    simpa [prefixWord, tailWord_4241539, baseEnd_4241539] using wordTrace_append hprefix tailTrace_4241539
  have hstable : (prefixWord ++ tailWord_4241539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4241539).length < 2 ^ (prefixWord ++ tailWord_4241539).sum := by decide
  have hdescent : baseEnd_4241539 < baseStart_4241539 := by decide
  rcases family_descends (prefixWord ++ tailWord_4241539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4241558 : List Nat := [5, 3, 2, 1, 2, 1, 2, 1, 1, 1, 4]
def baseStart_4241558 : Nat := 118140960795 + 4241558 * 2 ^ 59
def prefixEnd_4241558 : Nat := 4983230072969 + 3 ^ 40 * 4241558 * 2
def baseEnd_4241558 : Nat := 2177957977923221118518437

theorem tailTrace_4241558 : CollatzResearch.WordTrace tailWord_4241558 prefixEnd_4241558 2177957977923221118518437 := by
  unfold tailWord_4241558
  simp only [CollatzResearch.WordTrace]
  refine ⟨9668895597972952579940333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 103134886378378160852696885 9668895597972952579940333)
  ·
    refine ⟨3625835849239857217477625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9668895597972952579940333 3625835849239857217477625)
    ·
      refine ⟨2719376886929892913108219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3625835849239857217477625 2719376886929892913108219)
      ·
        refine ⟨4079065330394839369662329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2719376886929892913108219 4079065330394839369662329)
        ·
          refine ⟨3059298997796129527246747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4079065330394839369662329 3059298997796129527246747)
          ·
            refine ⟨4588948496694194290870121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3059298997796129527246747 4588948496694194290870121)
            ·
              refine ⟨3441711372520645718152591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4588948496694194290870121 3441711372520645718152591)
              ·
                refine ⟨5162567058780968577228887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3441711372520645718152591 5162567058780968577228887)
                ·
                  refine ⟨7743850588171452865843331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5162567058780968577228887 7743850588171452865843331)
                  ·
                    refine ⟨11615775882257179298764997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7743850588171452865843331 11615775882257179298764997)
                    ·
                      refine ⟨2177957977923221118518437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11615775882257179298764997 2177957977923221118518437)
                      ·
                        rfl

theorem cell23_4241558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_4241558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4241558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4241558 prefixEnd_4241558 := by exact prefixLift 4241558
  have htrace : WordTrace (prefixWord ++ tailWord_4241558) baseStart_4241558 baseEnd_4241558 := by
    simpa [prefixWord, tailWord_4241558, baseEnd_4241558] using wordTrace_append hprefix tailTrace_4241558
  have hstable : (prefixWord ++ tailWord_4241558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4241558).length < 2 ^ (prefixWord ++ tailWord_4241558).sum := by decide
  have hdescent : baseEnd_4241558 < baseStart_4241558 := by decide
  rcases family_descends (prefixWord ++ tailWord_4241558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4241567 : List Nat := [1, 1, 2, 6, 1, 3, 2, 1, 1, 3, 2]
def baseStart_4241567 : Nat := 118140960795 + 4241567 * 2 ^ 59
def prefixEnd_4241567 : Nat := 4983230072969 + 3 ^ 40 * 4241567 * 2
def baseEnd_4241567 : Nat := 2177962599249111583305895

theorem tailTrace_4241567 : CollatzResearch.WordTrace tailWord_4241567 prefixEnd_4241567 2177962599249111583305895 := by
  unfold tailWord_4241567
  simp only [CollatzResearch.WordTrace]
  refine ⟨154702657824534635816122955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103135105216356423877415303 154702657824534635816122955)
  ·
    refine ⟨232053986736801953724184433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154702657824534635816122955 232053986736801953724184433)
    ·
      refine ⟨174040490052601465293138325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232053986736801953724184433 174040490052601465293138325)
      ·
        refine ⟨8158147971215693685615859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 174040490052601465293138325 8158147971215693685615859)
        ·
          refine ⟨12237221956823540528423789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8158147971215693685615859 12237221956823540528423789)
          ·
            refine ⟨4588958233808827698158921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12237221956823540528423789 4588958233808827698158921)
            ·
              refine ⟨3441718675356620773619191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4588958233808827698158921 3441718675356620773619191)
              ·
                refine ⟨5162578013034931160428787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3441718675356620773619191 5162578013034931160428787)
                ·
                  refine ⟨7743867019552396740643181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5162578013034931160428787 7743867019552396740643181)
                  ·
                    refine ⟨2903950132332148777741193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7743867019552396740643181 2903950132332148777741193)
                    ·
                      refine ⟨2177962599249111583305895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2903950132332148777741193 2177962599249111583305895)
                      ·
                        rfl

theorem cell23_4241567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_4241567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4241567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4241567 prefixEnd_4241567 := by exact prefixLift 4241567
  have htrace : WordTrace (prefixWord ++ tailWord_4241567) baseStart_4241567 baseEnd_4241567 := by
    simpa [prefixWord, tailWord_4241567, baseEnd_4241567] using wordTrace_append hprefix tailTrace_4241567
  have hstable : (prefixWord ++ tailWord_4241567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4241567).length < 2 ^ (prefixWord ++ tailWord_4241567).sum := by decide
  have hdescent : baseEnd_4241567 < baseStart_4241567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4241567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4241586 : List Nat := [3, 2, 1, 1, 1, 3, 1, 6, 5]
def baseStart_4241586 : Nat := 118140960795 + 4241586 * 2 ^ 59
def prefixEnd_4241586 : Nat := 4983230072969 + 3 ^ 40 * 4241586 * 2
def baseEnd_4241586 : Nat := 241996928375727445440923

theorem tailTrace_4241586 : CollatzResearch.WordTrace tailWord_4241586 prefixEnd_4241586 241996928375727445440923 := by
  unfold tailWord_4241586
  simp only [CollatzResearch.WordTrace]
  refine ⟨38675837702866450515266153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103135567207643868040709741 38675837702866450515266153)
  ·
    refine ⟨29006878277149837886449615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38675837702866450515266153 29006878277149837886449615)
    ·
      refine ⟨43510317415724756829674423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29006878277149837886449615 43510317415724756829674423)
      ·
        refine ⟨65265476123587135244511635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43510317415724756829674423 65265476123587135244511635)
        ·
          refine ⟨97898214185380702866767453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65265476123587135244511635 97898214185380702866767453)
          ·
            refine ⟨36711830319517763575037795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97898214185380702866767453 36711830319517763575037795)
            ·
              refine ⟨55067745479276645362556693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36711830319517763575037795 55067745479276645362556693)
              ·
                refine ⟨2581300569341092751369845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 55067745479276645362556693 2581300569341092751369845)
                ·
                  refine ⟨241996928375727445440923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2581300569341092751369845 241996928375727445440923)
                  ·
                    rfl

theorem cell23_4241586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 6, 5].length) (baseStart_4241586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4241586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4241586 prefixEnd_4241586 := by exact prefixLift 4241586
  have htrace : WordTrace (prefixWord ++ tailWord_4241586) baseStart_4241586 baseEnd_4241586 := by
    simpa [prefixWord, tailWord_4241586, baseEnd_4241586] using wordTrace_append hprefix tailTrace_4241586
  have hstable : (prefixWord ++ tailWord_4241586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4241586).length < 2 ^ (prefixWord ++ tailWord_4241586).sum := by decide
  have hdescent : baseEnd_4241586 < baseStart_4241586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4241586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4241649 : List Nat := [1, 2, 2, 2, 2, 1, 2, 2, 2, 1, 6]
def baseStart_4241649 : Nat := 118140960795 + 4241649 * 2 ^ 59
def prefixEnd_4241649 : Nat := 4983230072969 + 3 ^ 40 * 4241649 * 2
def baseEnd_4241649 : Nat := 2178004704662780262480517

theorem tailTrace_4241649 : CollatzResearch.WordTrace tailWord_4241649 prefixEnd_4241649 2178004704662780262480517 := by
  unfold tailWord_4241649
  simp only [CollatzResearch.WordTrace]
  refine ⟨154705648610237563820608001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103137099073491709213738667 154705648610237563820608001)
  ·
    refine ⟨116029236457678172865456001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154705648610237563820608001 116029236457678172865456001)
    ·
      refine ⟨87021927343258629649092001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116029236457678172865456001 87021927343258629649092001)
      ·
        refine ⟨65266445507443972236819001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87021927343258629649092001 65266445507443972236819001)
        ·
          refine ⟨48949834130582979177614251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65266445507443972236819001 48949834130582979177614251)
          ·
            refine ⟨73424751195874468766421377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48949834130582979177614251 73424751195874468766421377)
            ·
              refine ⟨55068563396905851574816033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73424751195874468766421377 55068563396905851574816033)
              ·
                refine ⟨41301422547679388681112025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55068563396905851574816033 41301422547679388681112025)
                ·
                  refine ⟨30976066910759541510834019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41301422547679388681112025 30976066910759541510834019)
                  ·
                    refine ⟨46464100366139312266251029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30976066910759541510834019 46464100366139312266251029)
                    ·
                      refine ⟨2178004704662780262480517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46464100366139312266251029 2178004704662780262480517)
                      ·
                        rfl

theorem cell23_4241649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_4241649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4241649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4241649 prefixEnd_4241649 := by exact prefixLift 4241649
  have htrace : WordTrace (prefixWord ++ tailWord_4241649) baseStart_4241649 baseEnd_4241649 := by
    simpa [prefixWord, tailWord_4241649, baseEnd_4241649] using wordTrace_append hprefix tailTrace_4241649
  have hstable : (prefixWord ++ tailWord_4241649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4241649).length < 2 ^ (prefixWord ++ tailWord_4241649).sum := by decide
  have hdescent : baseEnd_4241649 < baseStart_4241649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4241649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4241673 : List Nat := [1, 2, 1, 1, 3, 5, 2, 1, 2, 2, 3]
def baseStart_4241673 : Nat := 118140960795 + 4241673 * 2 ^ 59
def prefixEnd_4241673 : Nat := 4983230072969 + 3 ^ 40 * 4241673 * 2
def baseEnd_4241673 : Nat := 2178017028198488168580407

theorem tailTrace_4241673 : CollatzResearch.WordTrace tailWord_4241673 prefixEnd_4241673 2178017028198488168580407 := by
  unfold tailWord_4241673
  simp only [CollatzResearch.WordTrace]
  refine ⟨154706523962150615919481673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103137682641433743946321115 154706523962150615919481673)
  ·
    refine ⟨116029892971612961939611255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154706523962150615919481673 116029892971612961939611255)
    ·
      refine ⟨174044839457419442909416883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116029892971612961939611255 174044839457419442909416883)
      ·
        refine ⟨261067259186129164364125325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174044839457419442909416883 261067259186129164364125325)
        ·
          refine ⟨97900222194798436636546997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 261067259186129164364125325 97900222194798436636546997)
          ·
            refine ⟨9178145830762353434676281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 97900222194798436636546997 9178145830762353434676281)
            ·
              refine ⟨6883609373071765076007211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9178145830762353434676281 6883609373071765076007211)
              ·
                refine ⟨10325414059607647614010817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6883609373071765076007211 10325414059607647614010817)
                ·
                  refine ⟨7744060544705735710508113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10325414059607647614010817 7744060544705735710508113)
                  ·
                    refine ⟨5808045408529301782881085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7744060544705735710508113 5808045408529301782881085)
                    ·
                      refine ⟨2178017028198488168580407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5808045408529301782881085 2178017028198488168580407)
                      ·
                        rfl

theorem cell23_4241673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 2, 2, 3].length) (baseStart_4241673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4241673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4241673 prefixEnd_4241673 := by exact prefixLift 4241673
  have htrace : WordTrace (prefixWord ++ tailWord_4241673) baseStart_4241673 baseEnd_4241673 := by
    simpa [prefixWord, tailWord_4241673, baseEnd_4241673] using wordTrace_append hprefix tailTrace_4241673
  have hstable : (prefixWord ++ tailWord_4241673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4241673).length < 2 ^ (prefixWord ++ tailWord_4241673).sum := by decide
  have hdescent : baseEnd_4241673 < baseStart_4241673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4241673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4241736 : List Nat := [2, 1, 3, 1, 1, 2, 4, 2, 1, 6]
def baseStart_4241736 : Nat := 118140960795 + 4241736 * 2 ^ 59
def prefixEnd_4241736 : Nat := 4983230072969 + 3 ^ 40 * 4241736 * 2
def baseEnd_4241736 : Nat := 726016459159907140697539

theorem tailTrace_4241736 : CollatzResearch.WordTrace tailWord_4241736 prefixEnd_4241736 726016459159907140697539 := by
  unfold tailWord_4241736
  simp only [CollatzResearch.WordTrace]
  refine ⟨77354410880461188839512531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103139214507281585119350041 77354410880461188839512531)
  ·
    refine ⟨116031616320691783259268797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77354410880461188839512531 116031616320691783259268797)
    ·
      refine ⟨43511856120259418722225799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116031616320691783259268797 43511856120259418722225799)
      ·
        refine ⟨65267784180389128083338699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43511856120259418722225799 65267784180389128083338699)
        ·
          refine ⟨97901676270583692125008049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65267784180389128083338699 97901676270583692125008049)
          ·
            refine ⟨73426257202937769093756037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97901676270583692125008049 73426257202937769093756037)
            ·
              refine ⟨13767423225550831705079257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73426257202937769093756037 13767423225550831705079257)
              ·
                refine ⟨10325567419163123778809443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13767423225550831705079257 10325567419163123778809443)
                ·
                  refine ⟨15488351128744685668214165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10325567419163123778809443 15488351128744685668214165)
                  ·
                    refine ⟨726016459159907140697539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15488351128744685668214165 726016459159907140697539)
                    ·
                      rfl

theorem cell23_4241736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 1, 6].length) (baseStart_4241736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4241736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4241736 prefixEnd_4241736 := by exact prefixLift 4241736
  have htrace : WordTrace (prefixWord ++ tailWord_4241736) baseStart_4241736 baseEnd_4241736 := by
    simpa [prefixWord, tailWord_4241736, baseEnd_4241736] using wordTrace_append hprefix tailTrace_4241736
  have hstable : (prefixWord ++ tailWord_4241736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4241736).length < 2 ^ (prefixWord ++ tailWord_4241736).sum := by decide
  have hdescent : baseEnd_4241736 < baseStart_4241736 := by decide
  rcases family_descends (prefixWord ++ tailWord_4241736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4241770 : List Nat := [3, 1, 3, 3, 1, 3, 1, 1, 1, 6]
def baseStart_4241770 : Nat := 118140960795 + 4241770 * 2 ^ 59
def prefixEnd_4241770 : Nat := 4983230072969 + 3 ^ 40 * 4241770 * 2
def baseEnd_4241770 : Nat := 726022278607324763022487

theorem tailTrace_4241770 : CollatzResearch.WordTrace tailWord_4241770 prefixEnd_4241770 726022278607324763022487 := by
  unfold tailWord_4241770
  simp only [CollatzResearch.WordTrace]
  refine ⟨38677515460699800371440691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103140041228532800990508509 38677515460699800371440691)
  ·
    refine ⟨58016273191049700557161037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38677515460699800371440691 58016273191049700557161037)
    ·
      refine ⟨21756102446643637708935389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58016273191049700557161037 21756102446643637708935389)
      ·
        refine ⟨8158538417491364140850771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21756102446643637708935389 8158538417491364140850771)
        ·
          refine ⟨12237807626237046211276157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8158538417491364140850771 12237807626237046211276157)
          ·
            refine ⟨4589177859838892329228559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12237807626237046211276157 4589177859838892329228559)
            ·
              refine ⟨6883766789758338493842839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4589177859838892329228559 6883766789758338493842839)
              ·
                refine ⟨10325650184637507740764259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6883766789758338493842839 10325650184637507740764259)
                ·
                  refine ⟨15488475276956261611146389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10325650184637507740764259 15488475276956261611146389)
                  ·
                    refine ⟨726022278607324763022487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15488475276956261611146389 726022278607324763022487)
                    ·
                      rfl

theorem cell23_4241770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_4241770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4241770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4241770 prefixEnd_4241770 := by exact prefixLift 4241770
  have htrace : WordTrace (prefixWord ++ tailWord_4241770) baseStart_4241770 baseEnd_4241770 := by
    simpa [prefixWord, tailWord_4241770, baseEnd_4241770] using wordTrace_append hprefix tailTrace_4241770
  have hstable : (prefixWord ++ tailWord_4241770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4241770).length < 2 ^ (prefixWord ++ tailWord_4241770).sum := by decide
  have hdescent : baseEnd_4241770 < baseStart_4241770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4241770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4241827 : List Nat := [1, 1, 1, 4, 1, 4, 4, 1, 2, 1, 3]
def baseStart_4241827 : Nat := 118140960795 + 4241827 * 2 ^ 59
def prefixEnd_4241827 : Nat := 4983230072969 + 3 ^ 40 * 4241827 * 2
def baseEnd_4241827 : Nat := 2178096104219280566054699

theorem tailTrace_4241827 : CollatzResearch.WordTrace tailWord_4241827 prefixEnd_4241827 2178096104219280566054699 := by
  unfold tailWord_4241827
  simp only [CollatzResearch.WordTrace]
  refine ⟨154712140803592700220587735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103141427202395133480391823 154712140803592700220587735)
  ·
    refine ⟨232068211205389050330881603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154712140803592700220587735 232068211205389050330881603)
    ·
      refine ⟨348102316808083575496322405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232068211205389050330881603 348102316808083575496322405)
      ·
        refine ⟨65269184401515670405560451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 348102316808083575496322405 65269184401515670405560451)
        ·
          refine ⟨97903776602273505608340677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65269184401515670405560451 97903776602273505608340677)
          ·
            refine ⟨18356958112926282301563877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 97903776602273505608340677 18356958112926282301563877)
            ·
              refine ⟨3441929646173677931543227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18356958112926282301563877 3441929646173677931543227)
              ·
                refine ⟨5162894469260516897314841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3441929646173677931543227 5162894469260516897314841)
                ·
                  refine ⟨3872170851945387672986131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5162894469260516897314841 3872170851945387672986131)
                  ·
                    refine ⟨5808256277918081509479197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3872170851945387672986131 5808256277918081509479197)
                    ·
                      refine ⟨2178096104219280566054699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5808256277918081509479197 2178096104219280566054699)
                      ·
                        rfl

theorem cell23_4241827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 1, 2, 1, 3].length) (baseStart_4241827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4241827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4241827 prefixEnd_4241827 := by exact prefixLift 4241827
  have htrace : WordTrace (prefixWord ++ tailWord_4241827) baseStart_4241827 baseEnd_4241827 := by
    simpa [prefixWord, tailWord_4241827, baseEnd_4241827] using wordTrace_append hprefix tailTrace_4241827
  have hstable : (prefixWord ++ tailWord_4241827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4241827).length < 2 ^ (prefixWord ++ tailWord_4241827).sum := by decide
  have hdescent : baseEnd_4241827 < baseStart_4241827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4241827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4241833 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 5, 4, 2]
def baseStart_4241833 : Nat := 118140960795 + 4241833 * 2 ^ 59
def prefixEnd_4241833 : Nat := 4983230072969 + 3 ^ 40 * 4241833 * 2
def baseEnd_4241833 : Nat := 2178099185103207542579671

theorem tailTrace_4241833 : CollatzResearch.WordTrace tailWord_4241833 prefixEnd_4241833 2178099185103207542579671 := by
  unfold tailWord_4241833
  simp only [CollatzResearch.WordTrace]
  refine ⟨154712359641570963245306153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103141573094380642163537435 154712359641570963245306153)
  ·
    refine ⟨116034269731178222433979615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154712359641570963245306153 116034269731178222433979615)
    ·
      refine ⟨174051404596767333650969423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116034269731178222433979615 174051404596767333650969423)
      ·
        refine ⟨261077106895151000476454135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174051404596767333650969423 261077106895151000476454135)
        ·
          refine ⟨391615660342726500714681203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261077106895151000476454135 391615660342726500714681203)
          ·
            refine ⟨587423490514089751072021805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391615660342726500714681203 587423490514089751072021805)
            ·
              refine ⟨220283808942783656652008177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 587423490514089751072021805 220283808942783656652008177)
              ·
                refine ⟨165212856707087742489006133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 220283808942783656652008177 165212856707087742489006133)
                ·
                  refine ⟨15488705316289475858344325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 165212856707087742489006133 15488705316289475858344325)
                  ·
                    refine ⟨2904132246804276723439561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15488705316289475858344325 2904132246804276723439561)
                    ·
                      refine ⟨2178099185103207542579671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2904132246804276723439561 2178099185103207542579671)
                      ·
                        rfl

theorem cell23_4241833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 4, 2].length) (baseStart_4241833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4241833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4241833 prefixEnd_4241833 := by exact prefixLift 4241833
  have htrace : WordTrace (prefixWord ++ tailWord_4241833) baseStart_4241833 baseEnd_4241833 := by
    simpa [prefixWord, tailWord_4241833, baseEnd_4241833] using wordTrace_append hprefix tailTrace_4241833
  have hstable : (prefixWord ++ tailWord_4241833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4241833).length < 2 ^ (prefixWord ++ tailWord_4241833).sum := by decide
  have hdescent : baseEnd_4241833 < baseStart_4241833 := by decide
  rcases family_descends (prefixWord ++ tailWord_4241833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4241844 : List Nat := [2, 5, 2, 2, 1, 1, 1, 2, 1, 3, 3]
def baseStart_4241844 : Nat := 118140960795 + 4241844 * 2 ^ 59
def prefixEnd_4241844 : Nat := 4983230072969 + 3 ^ 40 * 4241844 * 2
def baseEnd_4241844 : Nat := 2178104833390406999542121

theorem tailTrace_4241844 : CollatzResearch.WordTrace tailWord_4241844 prefixEnd_4241844 2178104833390406999542121 := by
  unfold tailWord_4241844
  simp only [CollatzResearch.WordTrace]
  refine ⟨77356380422265556061978293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103141840563020741415971057 77356380422265556061978293)
  ·
    refine ⟨7252160664587395880810465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77356380422265556061978293 7252160664587395880810465)
    ·
      refine ⟨5439120498440546910607849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7252160664587395880810465 5439120498440546910607849)
      ·
        refine ⟨4079340373830410182955887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5439120498440546910607849 4079340373830410182955887)
        ·
          refine ⟨6119010560745615274433831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4079340373830410182955887 6119010560745615274433831)
          ·
            refine ⟨9178515841118422911650747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6119010560745615274433831 9178515841118422911650747)
            ·
              refine ⟨13767773761677634367476121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9178515841118422911650747 13767773761677634367476121)
              ·
                refine ⟨10325830321258225775607091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13767773761677634367476121 10325830321258225775607091)
                ·
                  refine ⟨15488745481887338663410637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10325830321258225775607091 15488745481887338663410637)
                  ·
                    refine ⟨5808279555707751998778989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15488745481887338663410637 5808279555707751998778989)
                    ·
                      refine ⟨2178104833390406999542121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5808279555707751998778989 2178104833390406999542121)
                      ·
                        rfl

theorem cell23_4241844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_4241844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4241844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4241844 prefixEnd_4241844 := by exact prefixLift 4241844
  have htrace : WordTrace (prefixWord ++ tailWord_4241844) baseStart_4241844 baseEnd_4241844 := by
    simpa [prefixWord, tailWord_4241844, baseEnd_4241844] using wordTrace_append hprefix tailTrace_4241844
  have hstable : (prefixWord ++ tailWord_4241844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4241844).length < 2 ^ (prefixWord ++ tailWord_4241844).sum := by decide
  have hdescent : baseEnd_4241844 < baseStart_4241844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4241844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4241850 : List Nat := [3, 1, 1, 1, 2, 1, 1, 3, 6, 2, 2]
def baseStart_4241850 : Nat := 118140960795 + 4241850 * 2 ^ 59
def prefixEnd_4241850 : Nat := 4983230072969 + 3 ^ 40 * 4241850 * 2
def baseEnd_4241850 : Nat := 2178107914274333976067093

theorem tailTrace_4241850 : CollatzResearch.WordTrace tailWord_4241850 prefixEnd_4241850 2178107914274333976067093 := by
  unfold tailWord_4241850
  simp only [CollatzResearch.WordTrace]
  refine ⟨38678244920627343787168751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103141986455006250099116669 38678244920627343787168751)
  ·
    refine ⟨58017367380941015680753127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38678244920627343787168751 58017367380941015680753127)
    ·
      refine ⟨87026051071411523521129691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58017367380941015680753127 87026051071411523521129691)
      ·
        refine ⟨130539076607117285281694537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87026051071411523521129691 130539076607117285281694537)
        ·
          refine ⟨97904307455337963961270903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130539076607117285281694537 97904307455337963961270903)
          ·
            refine ⟨146856461183006945941906355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97904307455337963961270903 146856461183006945941906355)
            ·
              refine ⟨220284691774510418912859533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146856461183006945941906355 220284691774510418912859533)
              ·
                refine ⟨82606759415441407092322325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 220284691774510418912859533 82606759415441407092322325)
                ·
                  refine ⟨3872191847598815957452609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 82606759415441407092322325 3872191847598815957452609)
                  ·
                    refine ⟨2904143885699111968089457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3872191847598815957452609 2904143885699111968089457)
                    ·
                      refine ⟨2178107914274333976067093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2904143885699111968089457 2178107914274333976067093)
                      ·
                        rfl

theorem cell23_4241850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 6, 2, 2].length) (baseStart_4241850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4241850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4241850 prefixEnd_4241850 := by exact prefixLift 4241850
  have htrace : WordTrace (prefixWord ++ tailWord_4241850) baseStart_4241850 baseEnd_4241850 := by
    simpa [prefixWord, tailWord_4241850, baseEnd_4241850] using wordTrace_append hprefix tailTrace_4241850
  have hstable : (prefixWord ++ tailWord_4241850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4241850).length < 2 ^ (prefixWord ++ tailWord_4241850).sum := by decide
  have hdescent : baseEnd_4241850 < baseStart_4241850 := by decide
  rcases family_descends (prefixWord ++ tailWord_4241850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4241853 : List Nat := [1, 4, 1, 2, 2, 2, 2, 1, 2, 1, 5]
def baseStart_4241853 : Nat := 118140960795 + 4241853 * 2 ^ 59
def prefixEnd_4241853 : Nat := 4983230072969 + 3 ^ 40 * 4241853 * 2
def baseEnd_4241853 : Nat := 2178109454716297464329579

theorem tailTrace_4241853 : CollatzResearch.WordTrace tailWord_4241853 prefixEnd_4241853 2178109454716297464329579 := by
  unfold tailWord_4241853
  simp only [CollatzResearch.WordTrace]
  refine ⟨154713089101498506661034213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103142059400999004440689475 154713089101498506661034213)
  ·
    refine ⟨29008704206530969998943915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 154713089101498506661034213 29008704206530969998943915)
    ·
      refine ⟨43513056309796454998415873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29008704206530969998943915 43513056309796454998415873)
      ·
        refine ⟨32634792232347341248811905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43513056309796454998415873 32634792232347341248811905)
        ·
          refine ⟨24476094174260505936608929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32634792232347341248811905 24476094174260505936608929)
          ·
            refine ⟨18357070630695379452456697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24476094174260505936608929 18357070630695379452456697)
            ·
              refine ⟨13767802973021534589342523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18357070630695379452456697 13767802973021534589342523)
              ·
                refine ⟨20651704459532301884013785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13767802973021534589342523 20651704459532301884013785)
                ·
                  refine ⟨15488778344649226413010339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20651704459532301884013785 15488778344649226413010339)
                  ·
                    refine ⟨23233167516973839619515509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15488778344649226413010339 23233167516973839619515509)
                    ·
                      refine ⟨2178109454716297464329579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23233167516973839619515509 2178109454716297464329579)
                      ·
                        rfl

theorem cell23_4241853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_4241853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4241853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4241853 prefixEnd_4241853 := by exact prefixLift 4241853
  have htrace : WordTrace (prefixWord ++ tailWord_4241853) baseStart_4241853 baseEnd_4241853 := by
    simpa [prefixWord, tailWord_4241853, baseEnd_4241853] using wordTrace_append hprefix tailTrace_4241853
  have hstable : (prefixWord ++ tailWord_4241853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4241853).length < 2 ^ (prefixWord ++ tailWord_4241853).sum := by decide
  have hdescent : baseEnd_4241853 < baseStart_4241853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4241853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4241923 : List Nat := [1, 1, 1, 3, 2, 1, 4, 1, 4, 1, 4]
def baseStart_4241923 : Nat := 118140960795 + 4241923 * 2 ^ 59
def prefixEnd_4241923 : Nat := 4983230072969 + 3 ^ 40 * 4241923 * 2
def baseEnd_4241923 : Nat := 2178145398362112190454257

theorem tailTrace_4241923 : CollatzResearch.WordTrace tailWord_4241923 prefixEnd_4241923 2178145398362112190454257 := by
  unfold tailWord_4241923
  simp only [CollatzResearch.WordTrace]
  refine ⟨154715642211244908616082423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103143761474163272410721615 154715642211244908616082423)
  ·
    refine ⟨232073463316867362924123635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154715642211244908616082423 232073463316867362924123635)
    ·
      refine ⟨348110194975301044386185453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232073463316867362924123635 348110194975301044386185453)
      ·
        refine ⟨130541323115737891644819545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 348110194975301044386185453 130541323115737891644819545)
        ·
          refine ⟨97905992336803418733614659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130541323115737891644819545 97905992336803418733614659)
          ·
            refine ⟨146858988505205128100421989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97905992336803418733614659 146858988505205128100421989)
            ·
              refine ⟨27536060344725961518829123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 146858988505205128100421989 27536060344725961518829123)
              ·
                refine ⟨41304090517088942278243685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27536060344725961518829123 41304090517088942278243685)
                ·
                  refine ⟨7744516971954176677170691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41304090517088942278243685 7744516971954176677170691)
                  ·
                    refine ⟨11616775457931265015756037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7744516971954176677170691 11616775457931265015756037)
                    ·
                      refine ⟨2178145398362112190454257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11616775457931265015756037 2178145398362112190454257)
                      ·
                        rfl

theorem cell23_4241923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 4, 1, 4].length) (baseStart_4241923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4241923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4241923 prefixEnd_4241923 := by exact prefixLift 4241923
  have htrace : WordTrace (prefixWord ++ tailWord_4241923) baseStart_4241923 baseEnd_4241923 := by
    simpa [prefixWord, tailWord_4241923, baseEnd_4241923] using wordTrace_append hprefix tailTrace_4241923
  have hstable : (prefixWord ++ tailWord_4241923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4241923).length < 2 ^ (prefixWord ++ tailWord_4241923).sum := by decide
  have hdescent : baseEnd_4241923 < baseStart_4241923 := by decide
  rcases family_descends (prefixWord ++ tailWord_4241923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4241953 : List Nat := [1, 2, 3, 2, 2, 1, 1, 1, 2, 4, 4]
def baseStart_4241953 : Nat := 118140960795 + 4241953 * 2 ^ 59
def prefixEnd_4241953 : Nat := 4983230072969 + 3 ^ 40 * 4241953 * 2
def baseEnd_4241953 : Nat := 2178160802781747073079119

theorem tailTrace_4241953 : CollatzResearch.WordTrace tailWord_4241953 prefixEnd_4241953 2178160802781747073079119 := by
  unfold tailWord_4241953
  simp only [CollatzResearch.WordTrace]
  refine ⟨154716736401136223739674513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103144490934090815826449675 154716736401136223739674513)
  ·
    refine ⟨116037552300852167804755885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154716736401136223739674513 116037552300852167804755885)
    ·
      refine ⟨43514082112819562926783457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116037552300852167804755885 43514082112819562926783457)
      ·
        refine ⟨32635561584614672195087593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43514082112819562926783457 32635561584614672195087593)
        ·
          refine ⟨24476671188461004146315695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32635561584614672195087593 24476671188461004146315695)
          ·
            refine ⟨36715006782691506219473543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24476671188461004146315695 36715006782691506219473543)
            ·
              refine ⟨55072510174037259329210315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36715006782691506219473543 55072510174037259329210315)
              ·
                refine ⟨82608765261055888993815473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55072510174037259329210315 82608765261055888993815473)
                ·
                  refine ⟨61956573945791916745361605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82608765261055888993815473 61956573945791916745361605)
                  ·
                    refine ⟨11616857614835984389755301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61956573945791916745361605 11616857614835984389755301)
                    ·
                      refine ⟨2178160802781747073079119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11616857614835984389755301 2178160802781747073079119)
                      ·
                        rfl

theorem cell23_4241953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_4241953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4241953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4241953 prefixEnd_4241953 := by exact prefixLift 4241953
  have htrace : WordTrace (prefixWord ++ tailWord_4241953) baseStart_4241953 baseEnd_4241953 := by
    simpa [prefixWord, tailWord_4241953, baseEnd_4241953] using wordTrace_append hprefix tailTrace_4241953
  have hstable : (prefixWord ++ tailWord_4241953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4241953).length < 2 ^ (prefixWord ++ tailWord_4241953).sum := by decide
  have hdescent : baseEnd_4241953 < baseStart_4241953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4241953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4241997 : List Nat := [1, 6, 1, 1, 2, 2, 1, 3, 6]
def baseStart_4241997 : Nat := 118140960795 + 4241997 * 2 ^ 59
def prefixEnd_4241997 : Nat := 4983230072969 + 3 ^ 40 * 4241997 * 2
def baseEnd_4241997 : Nat := 242020377325616100103213

theorem tailTrace_4241997 : CollatzResearch.WordTrace tailWord_4241997 prefixEnd_4241997 242020377325616100103213 := by
  unfold tailWord_4241997
  simp only [CollatzResearch.WordTrace]
  refine ⟨154718341212976819254276245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103145560808651212836184163 154718341212976819254276245)
  ·
    refine ⟨7252422244358288402544199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 154718341212976819254276245 7252422244358288402544199)
    ·
      refine ⟨10878633366537432603816299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7252422244358288402544199 10878633366537432603816299)
      ·
        refine ⟨16317950049806148905724449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10878633366537432603816299 16317950049806148905724449)
        ·
          refine ⟨12238462537354611679293337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16317950049806148905724449 12238462537354611679293337)
          ·
            refine ⟨9178846903015958759470003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12238462537354611679293337 9178846903015958759470003)
            ·
              refine ⟨13768270354523938139205005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9178846903015958759470003 13768270354523938139205005)
              ·
                refine ⟨5163101382946476802201877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13768270354523938139205005 5163101382946476802201877)
                ·
                  refine ⟨242020377325616100103213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5163101382946476802201877 242020377325616100103213)
                  ·
                    rfl

theorem cell23_4241997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_4241997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4241997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4241997 prefixEnd_4241997 := by exact prefixLift 4241997
  have htrace : WordTrace (prefixWord ++ tailWord_4241997) baseStart_4241997 baseEnd_4241997 := by
    simpa [prefixWord, tailWord_4241997, baseEnd_4241997] using wordTrace_append hprefix tailTrace_4241997
  have hstable : (prefixWord ++ tailWord_4241997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4241997).length < 2 ^ (prefixWord ++ tailWord_4241997).sum := by decide
  have hdescent : baseEnd_4241997 < baseStart_4241997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4241997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4242000 : List Nat := [2, 1, 1, 1, 1, 3, 2, 4, 1, 5, 2]
def baseStart_4242000 : Nat := 118140960795 + 4242000 * 2 ^ 59
def prefixEnd_4242000 : Nat := 4983230072969 + 3 ^ 40 * 4242000 * 2
def baseEnd_4242000 : Nat := 2178184936372508389191403

theorem tailTrace_4242000 : CollatzResearch.WordTrace tailWord_4242000 prefixEnd_4242000 2178184936372508389191403 := by
  unfold tailWord_4242000
  simp only [CollatzResearch.WordTrace]
  refine ⟨77359225315982975383317727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103145633754643967177756969 77359225315982975383317727)
  ·
    refine ⟨116038837973974463074976591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77359225315982975383317727 116038837973974463074976591)
    ·
      refine ⟨174058256960961694612464887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116038837973974463074976591 174058256960961694612464887)
      ·
        refine ⟨261087385441442541918697331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174058256960961694612464887 261087385441442541918697331)
        ·
          refine ⟨391631078162163812878045997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261087385441442541918697331 391631078162163812878045997)
          ·
            refine ⟨146861654310811429829267249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 391631078162163812878045997 146861654310811429829267249)
            ·
              refine ⟨110146240733108572371950437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146861654310811429829267249 110146240733108572371950437)
              ·
                refine ⟨20652420137457857319740707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 110146240733108572371950437 20652420137457857319740707)
                ·
                  refine ⟨30978630206186785979611061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20652420137457857319740707 30978630206186785979611061)
                  ·
                    refine ⟨2904246581830011185588537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30978630206186785979611061 2904246581830011185588537)
                    ·
                      refine ⟨2178184936372508389191403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2904246581830011185588537 2178184936372508389191403)
                      ·
                        rfl

theorem cell23_4242000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 1, 5, 2].length) (baseStart_4242000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4242000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4242000 prefixEnd_4242000 := by exact prefixLift 4242000
  have htrace : WordTrace (prefixWord ++ tailWord_4242000) baseStart_4242000 baseEnd_4242000 := by
    simpa [prefixWord, tailWord_4242000, baseEnd_4242000] using wordTrace_append hprefix tailTrace_4242000
  have hstable : (prefixWord ++ tailWord_4242000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4242000).length < 2 ^ (prefixWord ++ tailWord_4242000).sum := by decide
  have hdescent : baseEnd_4242000 < baseStart_4242000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4242000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4242017 : List Nat := [1, 2, 3, 1, 1, 4, 1, 3, 2, 3, 2]
def baseStart_4242017 : Nat := 118140960795 + 4242017 * 2 ^ 59
def prefixEnd_4242017 : Nat := 4983230072969 + 3 ^ 40 * 4242017 * 2
def baseEnd_4242017 : Nat := 2178193665543634822678825

theorem tailTrace_4242017 : CollatzResearch.WordTrace tailWord_4242017 prefixEnd_4242017 2178193665543634822678825 := by
  unfold tailWord_4242017
  simp only [CollatzResearch.WordTrace]
  refine ⟨154719070672904362670004305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103146047115269575113336203 154719070672904362670004305)
  ·
    refine ⟨116039303004678272002503229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154719070672904362670004305 116039303004678272002503229)
    ·
      refine ⟨43514738626754352000938711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116039303004678272002503229 43514738626754352000938711)
      ·
        refine ⟨65272107940131528001408067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43514738626754352000938711 65272107940131528001408067)
        ·
          refine ⟨97908161910197292002112101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65272107940131528001408067 97908161910197292002112101)
          ·
            refine ⟨18357780358161992250396019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 97908161910197292002112101 18357780358161992250396019)
            ·
              refine ⟨27536670537242988375594029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18357780358161992250396019 27536670537242988375594029)
              ·
                refine ⟨10326251451466120640847761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27536670537242988375594029 10326251451466120640847761)
                ·
                  refine ⟨7744688588599590480635821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10326251451466120640847761 7744688588599590480635821)
                  ·
                    refine ⟨2904258220724846430238433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7744688588599590480635821 2904258220724846430238433)
                    ·
                      refine ⟨2178193665543634822678825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2904258220724846430238433 2178193665543634822678825)
                      ·
                        rfl

theorem cell23_4242017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 2, 3, 2].length) (baseStart_4242017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4242017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4242017 prefixEnd_4242017 := by exact prefixLift 4242017
  have htrace : WordTrace (prefixWord ++ tailWord_4242017) baseStart_4242017 baseEnd_4242017 := by
    simpa [prefixWord, tailWord_4242017, baseEnd_4242017] using wordTrace_append hprefix tailTrace_4242017
  have hstable : (prefixWord ++ tailWord_4242017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4242017).length < 2 ^ (prefixWord ++ tailWord_4242017).sum := by decide
  have hdescent : baseEnd_4242017 < baseStart_4242017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4242017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4242041 : List Nat := [1, 2, 1, 3, 3, 2, 4, 2, 1, 1, 3]
def baseStart_4242041 : Nat := 118140960795 + 4242041 * 2 ^ 59
def prefixEnd_4242041 : Nat := 4983230072969 + 3 ^ 40 * 4242041 * 2
def baseEnd_4242041 : Nat := 2178205989079342728778715

theorem tailTrace_4242041 : CollatzResearch.WordTrace tailWord_4242041 prefixEnd_4242041 2178205989079342728778715 := by
  unfold tailWord_4242041
  simp only [CollatzResearch.WordTrace]
  refine ⟨154719946024817414768877977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103146630683211609845918651 154719946024817414768877977)
  ·
    refine ⟨116039959518613061076658483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154719946024817414768877977 116039959518613061076658483)
    ·
      refine ⟨174059939277919591614987725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116039959518613061076658483 174059939277919591614987725)
      ·
        refine ⟨65272477229219846855620397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 174059939277919591614987725 65272477229219846855620397)
        ·
          refine ⟨24477178960957442570857649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65272477229219846855620397 24477178960957442570857649)
          ·
            refine ⟨18357884220718081928143237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24477178960957442570857649 18357884220718081928143237)
            ·
              refine ⟨3442103291384640361526857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18357884220718081928143237 3442103291384640361526857)
              ·
                refine ⟨2581577468538480271145143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3442103291384640361526857 2581577468538480271145143)
                ·
                  refine ⟨3872366202807720406717715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2581577468538480271145143 3872366202807720406717715)
                  ·
                    refine ⟨5808549304211580610076573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3872366202807720406717715 5808549304211580610076573)
                    ·
                      refine ⟨2178205989079342728778715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5808549304211580610076573 2178205989079342728778715)
                      ·
                        rfl

theorem cell23_4242041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 2, 1, 1, 3].length) (baseStart_4242041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4242041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4242041 prefixEnd_4242041 := by exact prefixLift 4242041
  have htrace : WordTrace (prefixWord ++ tailWord_4242041) baseStart_4242041 baseEnd_4242041 := by
    simpa [prefixWord, tailWord_4242041, baseEnd_4242041] using wordTrace_append hprefix tailTrace_4242041
  have hstable : (prefixWord ++ tailWord_4242041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4242041).length < 2 ^ (prefixWord ++ tailWord_4242041).sum := by decide
  have hdescent : baseEnd_4242041 < baseStart_4242041 := by decide
  rcases family_descends (prefixWord ++ tailWord_4242041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4242043 : List Nat := [1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 6]
def baseStart_4242043 : Nat := 118140960795 + 4242043 * 2 ^ 59
def prefixEnd_4242043 : Nat := 4983230072969 + 3 ^ 40 * 4242043 * 2
def baseEnd_4242043 : Nat := 2178207016040651720953705

theorem tailTrace_4242043 : CollatzResearch.WordTrace tailWord_4242043 prefixEnd_4242043 2178207016040651720953705 := by
  unfold tailWord_4242043
  simp only [CollatzResearch.WordTrace]
  refine ⟨154720018970810169110450783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103146679313873446073633855 154720018970810169110450783)
  ·
    refine ⟨232080028456215253665676175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154720018970810169110450783 232080028456215253665676175)
    ·
      refine ⟨348120042684322880498514263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232080028456215253665676175 348120042684322880498514263)
      ·
        refine ⟨522180064026484320747771395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 348120042684322880498514263 522180064026484320747771395)
        ·
          refine ⟨783270096039726481121657093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 522180064026484320747771395 783270096039726481121657093)
          ·
            refine ⟨146863143007448715210310705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 783270096039726481121657093 146863143007448715210310705)
            ·
              refine ⟨110147357255586536407733029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146863143007448715210310705 110147357255586536407733029)
              ·
                refine ⟨20652629485422475576449943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 110147357255586536407733029 20652629485422475576449943)
                ·
                  refine ⟨30978944228133713364674915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20652629485422475576449943 30978944228133713364674915)
                  ·
                    refine ⟨46468416342200570047012373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30978944228133713364674915 46468416342200570047012373)
                    ·
                      refine ⟨2178207016040651720953705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46468416342200570047012373 2178207016040651720953705)
                      ·
                        rfl

theorem cell23_4242043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 6].length) (baseStart_4242043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4242043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4242043 prefixEnd_4242043 := by exact prefixLift 4242043
  have htrace : WordTrace (prefixWord ++ tailWord_4242043) baseStart_4242043 baseEnd_4242043 := by
    simpa [prefixWord, tailWord_4242043, baseEnd_4242043] using wordTrace_append hprefix tailTrace_4242043
  have hstable : (prefixWord ++ tailWord_4242043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4242043).length < 2 ^ (prefixWord ++ tailWord_4242043).sum := by decide
  have hdescent : baseEnd_4242043 < baseStart_4242043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4242043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4242081 : List Nat := [1, 2, 3, 3, 3, 2, 2, 1, 1, 1, 4]
def baseStart_4242081 : Nat := 118140960795 + 4242081 * 2 ^ 59
def prefixEnd_4242081 : Nat := 4983230072969 + 3 ^ 40 * 4242081 * 2
def baseEnd_4242081 : Nat := 2178226528305522572278531

theorem tailTrace_4242081 : CollatzResearch.WordTrace tailWord_4242081 prefixEnd_4242081 2178226528305522572278531 := by
  unfold tailWord_4242081
  simp only [CollatzResearch.WordTrace]
  refine ⟨154721404944672501600334097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103147603296448334400222731 154721404944672501600334097)
  ·
    refine ⟨116041053708504376200250573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154721404944672501600334097 116041053708504376200250573)
    ·
      refine ⟨43515395140689141075093965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116041053708504376200250573 43515395140689141075093965)
      ·
        refine ⟨16318273177758427903160237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43515395140689141075093965 16318273177758427903160237)
        ·
          refine ⟨6119352441659410463685089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16318273177758427903160237 6119352441659410463685089)
          ·
            refine ⟨4589514331244557847763817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6119352441659410463685089 4589514331244557847763817)
            ·
              refine ⟨3442135748433418385822863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4589514331244557847763817 3442135748433418385822863)
              ·
                refine ⟨5163203622650127578734295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3442135748433418385822863 5163203622650127578734295)
                ·
                  refine ⟨7744805433975191368101443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5163203622650127578734295 7744805433975191368101443)
                  ·
                    refine ⟨11617208150962787052152165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7744805433975191368101443 11617208150962787052152165)
                    ·
                      refine ⟨2178226528305522572278531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11617208150962787052152165 2178226528305522572278531)
                      ·
                        rfl

theorem cell23_4242081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_4242081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4242081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4242081 prefixEnd_4242081 := by exact prefixLift 4242081
  have htrace : WordTrace (prefixWord ++ tailWord_4242081) baseStart_4242081 baseEnd_4242081 := by
    simpa [prefixWord, tailWord_4242081, baseEnd_4242081] using wordTrace_append hprefix tailTrace_4242081
  have hstable : (prefixWord ++ tailWord_4242081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4242081).length < 2 ^ (prefixWord ++ tailWord_4242081).sum := by decide
  have hdescent : baseEnd_4242081 < baseStart_4242081 := by decide
  rcases family_descends (prefixWord ++ tailWord_4242081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4242083 : List Nat := [1, 1, 1, 4, 1, 1, 2, 2, 1, 9]
def baseStart_4242083 : Nat := 118140960795 + 4242083 * 2 ^ 59
def prefixEnd_4242083 : Nat := 4983230072969 + 3 ^ 40 * 4242083 * 2
def baseEnd_4242083 : Nat := 726075851755610521484507

theorem tailTrace_4242083 : CollatzResearch.WordTrace tailWord_4242083 prefixEnd_4242083 726075851755610521484507 := by
  unfold tailWord_4242083
  simp only [CollatzResearch.WordTrace]
  refine ⟨154721477890665255941906903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103147651927110170627937935 154721477890665255941906903)
  ·
    refine ⟨232082216835997883912860355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154721477890665255941906903 232082216835997883912860355)
    ·
      refine ⟨348123325253996825869290533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232082216835997883912860355 348123325253996825869290533)
      ·
        refine ⟨65273123485124404850491975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 348123325253996825869290533 65273123485124404850491975)
        ·
          refine ⟨97909685227686607275737963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65273123485124404850491975 97909685227686607275737963)
          ·
            refine ⟨146864527841529910913606945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97909685227686607275737963 146864527841529910913606945)
            ·
              refine ⟨110148395881147433185205209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146864527841529910913606945 110148395881147433185205209)
              ·
                refine ⟨82611296910860574888903907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110148395881147433185205209 82611296910860574888903907)
                ·
                  refine ⟨123916945366290862333355861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82611296910860574888903907 123916945366290862333355861)
                  ·
                    refine ⟨726075851755610521484507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 123916945366290862333355861 726075851755610521484507)
                    ·
                      rfl

theorem cell23_4242083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 9].length) (baseStart_4242083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4242083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4242083 prefixEnd_4242083 := by exact prefixLift 4242083
  have htrace : WordTrace (prefixWord ++ tailWord_4242083) baseStart_4242083 baseEnd_4242083 := by
    simpa [prefixWord, tailWord_4242083, baseEnd_4242083] using wordTrace_append hprefix tailTrace_4242083
  have hstable : (prefixWord ++ tailWord_4242083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4242083).length < 2 ^ (prefixWord ++ tailWord_4242083).sum := by decide
  have hdescent : baseEnd_4242083 < baseStart_4242083 := by decide
  rcases family_descends (prefixWord ++ tailWord_4242083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4242087 : List Nat := [1, 1, 6, 3, 1, 1, 10]
def baseStart_4242087 : Nat := 118140960795 + 4242087 * 2 ^ 59
def prefixEnd_4242087 : Nat := 4983230072969 + 3 ^ 40 * 4242087 * 2
def baseEnd_4242087 : Nat := 26891723570240117886463

theorem tailTrace_4242087 : CollatzResearch.WordTrace tailWord_4242087 prefixEnd_4242087 26891723570240117886463 := by
  unfold tailWord_4242087
  simp only [CollatzResearch.WordTrace]
  refine ⟨154721623782650764625052515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103147749188433843083368343 154721623782650764625052515)
  ·
    refine ⟨232082435673976146937578773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154721623782650764625052515 232082435673976146937578773)
    ·
      refine ⟨10878864172217631887699005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 232082435673976146937578773 10878864172217631887699005)
      ·
        refine ⟨4079574064581611957887127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10878864172217631887699005 4079574064581611957887127)
        ·
          refine ⟨6119361096872417936830691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4079574064581611957887127 6119361096872417936830691)
          ·
            refine ⟨9179041645308626905246037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6119361096872417936830691 9179041645308626905246037)
            ·
              refine ⟨26891723570240117886463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9179041645308626905246037 26891723570240117886463)
              ·
                rfl

theorem cell23_4242087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 10].length) (baseStart_4242087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4242087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4242087 prefixEnd_4242087 := by exact prefixLift 4242087
  have htrace : WordTrace (prefixWord ++ tailWord_4242087) baseStart_4242087 baseEnd_4242087 := by
    simpa [prefixWord, tailWord_4242087, baseEnd_4242087] using wordTrace_append hprefix tailTrace_4242087
  have hstable : (prefixWord ++ tailWord_4242087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4242087).length < 2 ^ (prefixWord ++ tailWord_4242087).sum := by decide
  have hdescent : baseEnd_4242087 < baseStart_4242087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4242087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4242132 : List Nat := [2, 4, 1, 3, 3, 1, 1, 3, 1, 2, 2]
def baseStart_4242132 : Nat := 118140960795 + 4242132 * 2 ^ 59
def prefixEnd_4242132 : Nat := 4983230072969 + 3 ^ 40 * 4242132 * 2
def baseEnd_4242132 : Nat := 2178252715818901872740797

theorem tailTrace_4242132 : CollatzResearch.WordTrace tailWord_4242132 prefixEnd_4242132 2178252715818901872740797 := by
  unfold tailWord_4242132
  simp only [CollatzResearch.WordTrace]
  refine ⟨77361632533743868655220325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103148843378325158206960433 77361632533743868655220325)
  ·
    refine ⟨14505306100076975372853811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77361632533743868655220325 14505306100076975372853811)
    ·
      refine ⟨21757959150115463059280717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14505306100076975372853811 21757959150115463059280717)
      ·
        refine ⟨8159234681293298647230269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21757959150115463059280717 8159234681293298647230269)
        ·
          refine ⟨3059713005484986992711351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8159234681293298647230269 3059713005484986992711351)
          ·
            refine ⟨4589569508227480489067027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3059713005484986992711351 4589569508227480489067027)
            ·
              refine ⟨6884354262341220733600541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4589569508227480489067027 6884354262341220733600541)
              ·
                refine ⟨2581632848377957775100203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6884354262341220733600541 2581632848377957775100203)
                ·
                  refine ⟨3872449272566936662650305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2581632848377957775100203 3872449272566936662650305)
                  ·
                    refine ⟨2904336954425202496987729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3872449272566936662650305 2904336954425202496987729)
                    ·
                      refine ⟨2178252715818901872740797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2904336954425202496987729 2178252715818901872740797)
                      ·
                        rfl

theorem cell23_4242132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_4242132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4242132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4242132 prefixEnd_4242132 := by exact prefixLift 4242132
  have htrace : WordTrace (prefixWord ++ tailWord_4242132) baseStart_4242132 baseEnd_4242132 := by
    simpa [prefixWord, tailWord_4242132, baseEnd_4242132] using wordTrace_append hprefix tailTrace_4242132
  have hstable : (prefixWord ++ tailWord_4242132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4242132).length < 2 ^ (prefixWord ++ tailWord_4242132).sum := by decide
  have hdescent : baseEnd_4242132 < baseStart_4242132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4242132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4242137 : List Nat := [1, 2, 1, 2, 3, 2, 2, 1, 3, 4, 2]
def baseStart_4242137 : Nat := 118140960795 + 4242137 * 2 ^ 59
def prefixEnd_4242137 : Nat := 4983230072969 + 3 ^ 40 * 4242137 * 2
def baseEnd_4242137 : Nat := 2178255283222174353178273

theorem tailTrace_4242137 : CollatzResearch.WordTrace tailWord_4242137 prefixEnd_4242137 2178255283222174353178273 := by
  unfold tailWord_4242137
  simp only [CollatzResearch.WordTrace]
  refine ⟨154723447432469623164372665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103148964954979748776248443 154723447432469623164372665)
  ·
    refine ⟨116042585574352217373279499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154723447432469623164372665 116042585574352217373279499)
    ·
      refine ⟨174063878361528326059919249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116042585574352217373279499 174063878361528326059919249)
      ·
        refine ⟨130547908771146244544939437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174063878361528326059919249 130547908771146244544939437)
        ·
          refine ⟨48955465789179841704352289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130547908771146244544939437 48955465789179841704352289)
          ·
            refine ⟨36716599341884881278264217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48955465789179841704352289 36716599341884881278264217)
            ·
              refine ⟨27537449506413660958698163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36716599341884881278264217 27537449506413660958698163)
              ·
                refine ⟨41306174259620491438047245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27537449506413660958698163 41306174259620491438047245)
                ·
                  refine ⟨15489815347357684289267717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41306174259620491438047245 15489815347357684289267717)
                  ·
                    refine ⟨2904340377629565804237697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15489815347357684289267717 2904340377629565804237697)
                    ·
                      refine ⟨2178255283222174353178273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2904340377629565804237697 2178255283222174353178273)
                      ·
                        rfl

theorem cell23_4242137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 4, 2].length) (baseStart_4242137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4242137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4242137 prefixEnd_4242137 := by exact prefixLift 4242137
  have htrace : WordTrace (prefixWord ++ tailWord_4242137) baseStart_4242137 baseEnd_4242137 := by
    simpa [prefixWord, tailWord_4242137, baseEnd_4242137] using wordTrace_append hprefix tailTrace_4242137
  have hstable : (prefixWord ++ tailWord_4242137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4242137).length < 2 ^ (prefixWord ++ tailWord_4242137).sum := by decide
  have hdescent : baseEnd_4242137 < baseStart_4242137 := by decide
  rcases family_descends (prefixWord ++ tailWord_4242137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4242157 : List Nat := [1, 5, 1, 2, 1, 1, 2, 1, 2, 4, 3]
def baseStart_4242157 : Nat := 118140960795 + 4242157 * 2 ^ 59
def prefixEnd_4242157 : Nat := 4983230072969 + 3 ^ 40 * 4242157 * 2
def baseEnd_4242157 : Nat := 2178265552835264274928181

theorem tailTrace_4242157 : CollatzResearch.WordTrace tailWord_4242157 prefixEnd_4242157 2178265552835264274928181 := by
  unfold tailWord_4242157
  simp only [CollatzResearch.WordTrace]
  refine ⟨154724176892397166580100725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103149451261598111053400483 154724176892397166580100725)
  ·
    refine ⟨14505391583662234366884443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 154724176892397166580100725 14505391583662234366884443)
    ·
      refine ⟨21758087375493351550326665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14505391583662234366884443 21758087375493351550326665)
      ·
        refine ⟨16318565531620013662744999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21758087375493351550326665 16318565531620013662744999)
        ·
          refine ⟨24477848297430020494117499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16318565531620013662744999 24477848297430020494117499)
          ·
            refine ⟨36716772446145030741176249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24477848297430020494117499 36716772446145030741176249)
            ·
              refine ⟨27537579334608773055882187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36716772446145030741176249 27537579334608773055882187)
              ·
                refine ⟨41306369001913159583823281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27537579334608773055882187 41306369001913159583823281)
                ·
                  refine ⟨30979776751434869687867461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41306369001913159583823281 30979776751434869687867461)
                  ·
                    refine ⟨5808708140894038066475149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30979776751434869687867461 5808708140894038066475149)
                    ·
                      refine ⟨2178265552835264274928181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5808708140894038066475149 2178265552835264274928181)
                      ·
                        rfl

theorem cell23_4242157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_4242157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4242157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4242157 prefixEnd_4242157 := by exact prefixLift 4242157
  have htrace : WordTrace (prefixWord ++ tailWord_4242157) baseStart_4242157 baseEnd_4242157 := by
    simpa [prefixWord, tailWord_4242157, baseEnd_4242157] using wordTrace_append hprefix tailTrace_4242157
  have hstable : (prefixWord ++ tailWord_4242157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4242157).length < 2 ^ (prefixWord ++ tailWord_4242157).sum := by decide
  have hdescent : baseEnd_4242157 < baseStart_4242157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4242157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4242165 : List Nat := [1, 3, 6, 1, 1, 1, 1, 3, 2, 1, 3]
def baseStart_4242165 : Nat := 118140960795 + 4242165 * 2 ^ 59
def prefixEnd_4242165 : Nat := 4983230072969 + 3 ^ 40 * 4242165 * 2
def baseEnd_4242165 : Nat := 2178269660680500243628145

theorem tailTrace_4242165 : CollatzResearch.WordTrace tailWord_4242165 prefixEnd_4242165 2178269660680500243628145 := by
  unfold tailWord_4242165
  simp only [CollatzResearch.WordTrace]
  refine ⟨154724468676368183946391949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103149645784245455964261299 154724468676368183946391949)
  ·
    refine ⟨58021675753638068979896981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154724468676368183946391949 58021675753638068979896981)
    ·
      refine ⟨2719766050951784483432671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 58021675753638068979896981 2719766050951784483432671)
      ·
        refine ⟨4079649076427676725149007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2719766050951784483432671 4079649076427676725149007)
        ·
          refine ⟨6119473614641515087723511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4079649076427676725149007 6119473614641515087723511)
          ·
            refine ⟨9179210421962272631585267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6119473614641515087723511 9179210421962272631585267)
            ·
              refine ⟨13768815632943408947377901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9179210421962272631585267 13768815632943408947377901)
              ·
                refine ⟨5163305862353778355266713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13768815632943408947377901 5163305862353778355266713)
                ·
                  refine ⟨3872479396765333766450035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5163305862353778355266713 3872479396765333766450035)
                  ·
                    refine ⟨5808719095148000649675053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3872479396765333766450035 5808719095148000649675053)
                    ·
                      refine ⟨2178269660680500243628145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5808719095148000649675053 2178269660680500243628145)
                      ·
                        rfl

theorem cell23_4242165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_4242165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4242165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4242165 prefixEnd_4242165 := by exact prefixLift 4242165
  have htrace : WordTrace (prefixWord ++ tailWord_4242165) baseStart_4242165 baseEnd_4242165 := by
    simpa [prefixWord, tailWord_4242165, baseEnd_4242165] using wordTrace_append hprefix tailTrace_4242165
  have hstable : (prefixWord ++ tailWord_4242165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4242165).length < 2 ^ (prefixWord ++ tailWord_4242165).sum := by decide
  have hdescent : baseEnd_4242165 < baseStart_4242165 := by decide
  rcases family_descends (prefixWord ++ tailWord_4242165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4242205 : List Nat := [1, 4, 2, 4, 1, 1, 2, 2, 2, 2, 2]
def baseStart_4242205 : Nat := 118140960795 + 4242205 * 2 ^ 59
def prefixEnd_4242205 : Nat := 4983230072969 + 3 ^ 40 * 4242205 * 2
def baseEnd_4242205 : Nat := 2178290199906680087127961

theorem tailTrace_4242205 : CollatzResearch.WordTrace tailWord_4242205 prefixEnd_4242205 2178290199906680087127961 := by
  unfold tailWord_4242205
  simp only [CollatzResearch.WordTrace]
  refine ⟨154725927596223270777848069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103150618397482180518565379 154725927596223270777848069)
  ·
    refine ⟨29011111424291863270846513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 154725927596223270777848069 29011111424291863270846513)
    ·
      refine ⟨21758333568218897453134885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29011111424291863270846513 21758333568218897453134885)
      ·
        refine ⟨4079687544041043272462791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21758333568218897453134885 4079687544041043272462791)
        ·
          refine ⟨6119531316061564908694187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4079687544041043272462791 6119531316061564908694187)
          ·
            refine ⟨9179296974092347363041281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6119531316061564908694187 9179296974092347363041281)
            ·
              refine ⟨6884472730569260522280961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9179296974092347363041281 6884472730569260522280961)
              ·
                refine ⟨5163354547926945391710721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6884472730569260522280961 5163354547926945391710721)
                ·
                  refine ⟨3872515910945209043783041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5163354547926945391710721 3872515910945209043783041)
                  ·
                    refine ⟨2904386933208906782837281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3872515910945209043783041 2904386933208906782837281)
                    ·
                      refine ⟨2178290199906680087127961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2904386933208906782837281 2178290199906680087127961)
                      ·
                        rfl

theorem cell23_4242205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_4242205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4242205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4242205 prefixEnd_4242205 := by exact prefixLift 4242205
  have htrace : WordTrace (prefixWord ++ tailWord_4242205) baseStart_4242205 baseEnd_4242205 := by
    simpa [prefixWord, tailWord_4242205, baseEnd_4242205] using wordTrace_append hprefix tailTrace_4242205
  have hstable : (prefixWord ++ tailWord_4242205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4242205).length < 2 ^ (prefixWord ++ tailWord_4242205).sum := by decide
  have hdescent : baseEnd_4242205 < baseStart_4242205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4242205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4242207 : List Nat := [1, 1, 2, 4, 2, 2, 2, 2, 2, 5]
def baseStart_4242207 : Nat := 118140960795 + 4242207 * 2 ^ 59
def prefixEnd_4242207 : Nat := 4983230072969 + 3 ^ 40 * 4242207 * 2
def baseEnd_4242207 : Nat := 726097075622663026434317

theorem tailTrace_4242207 : CollatzResearch.WordTrace tailWord_4242207 prefixEnd_4242207 726097075622663026434317 := by
  unfold tailWord_4242207
  simp only [CollatzResearch.WordTrace]
  refine ⟨154726000542216025119420875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103150667028144016746280583 154726000542216025119420875)
  ·
    refine ⟨232089000813324037679131313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154726000542216025119420875 232089000813324037679131313)
    ·
      refine ⟨174066750609993028259348485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232089000813324037679131313 174066750609993028259348485)
      ·
        refine ⟨32637515739373692798627841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 174066750609993028259348485 32637515739373692798627841)
        ·
          refine ⟨24478136804530269598970881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32637515739373692798627841 24478136804530269598970881)
          ·
            refine ⟨18358602603397702199228161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24478136804530269598970881 18358602603397702199228161)
            ·
              refine ⟨13768951952548276649421121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18358602603397702199228161 13768951952548276649421121)
              ·
                refine ⟨10326713964411207487065841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13768951952548276649421121 10326713964411207487065841)
                ·
                  refine ⟨7745035473308405615299381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10326713964411207487065841 7745035473308405615299381)
                  ·
                    refine ⟨726097075622663026434317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7745035473308405615299381 726097075622663026434317)
                    ·
                      rfl

theorem cell23_4242207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 2, 5].length) (baseStart_4242207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4242207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4242207 prefixEnd_4242207 := by exact prefixLift 4242207
  have htrace : WordTrace (prefixWord ++ tailWord_4242207) baseStart_4242207 baseEnd_4242207 := by
    simpa [prefixWord, tailWord_4242207, baseEnd_4242207] using wordTrace_append hprefix tailTrace_4242207
  have hstable : (prefixWord ++ tailWord_4242207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4242207).length < 2 ^ (prefixWord ++ tailWord_4242207).sum := by decide
  have hdescent : baseEnd_4242207 < baseStart_4242207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4242207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4242240 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 6]
def baseStart_4242240 : Nat := 118140960795 + 4242240 * 2 ^ 59
def prefixEnd_4242240 : Nat := 4983230072969 + 3 ^ 40 * 4242240 * 2
def baseEnd_4242240 : Nat := 2178308171729587450190299

theorem tailTrace_4242240 : CollatzResearch.WordTrace tailWord_4242240 prefixEnd_4242240 2178308171729587450190299 := by
  unfold tailWord_4242240
  simp only [CollatzResearch.WordTrace]
  refine ⟨77363602075548235877686087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103151469434064314503581449 77363602075548235877686087)
  ·
    refine ⟨116045403113322353816529131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77363602075548235877686087 116045403113322353816529131)
    ·
      refine ⟨174068104669983530724793697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116045403113322353816529131 174068104669983530724793697)
      ·
        refine ⟨130551078502487648043595273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174068104669983530724793697 130551078502487648043595273)
        ·
          refine ⟨97913308876865736032696455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130551078502487648043595273 97913308876865736032696455)
          ·
            refine ⟨146869963315298604049044683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97913308876865736032696455 146869963315298604049044683)
            ·
              refine ⟨220304944972947906073567025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146869963315298604049044683 220304944972947906073567025)
              ·
                refine ⟨165228708729710929555175269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 220304944972947906073567025 165228708729710929555175269)
                ·
                  refine ⟨30980382886820799291595363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 165228708729710929555175269 30980382886820799291595363)
                  ·
                    refine ⟨46470574330231198937393045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30980382886820799291595363 46470574330231198937393045)
                    ·
                      refine ⟨2178308171729587450190299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46470574330231198937393045 2178308171729587450190299)
                      ·
                        rfl

theorem cell23_4242240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 6].length) (baseStart_4242240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4242240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4242240 prefixEnd_4242240 := by exact prefixLift 4242240
  have htrace : WordTrace (prefixWord ++ tailWord_4242240) baseStart_4242240 baseEnd_4242240 := by
    simpa [prefixWord, tailWord_4242240, baseEnd_4242240] using wordTrace_append hprefix tailTrace_4242240
  have hstable : (prefixWord ++ tailWord_4242240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4242240).length < 2 ^ (prefixWord ++ tailWord_4242240).sum := by decide
  have hdescent : baseEnd_4242240 < baseStart_4242240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4242240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4242284 : List Nat := [2, 2, 1, 1, 4, 1, 5, 1, 6]
def baseStart_4242284 : Nat := 118140960795 + 4242284 * 2 ^ 59
def prefixEnd_4242284 : Nat := 4983230072969 + 3 ^ 40 * 4242284 * 2
def baseEnd_4242284 : Nat := 242036751653153919782233

theorem tailTrace_4242284 : CollatzResearch.WordTrace tailWord_4242284 prefixEnd_4242284 242036751653153919782233 := by
  unfold tailWord_4242284
  simp only [CollatzResearch.WordTrace]
  refine ⟨77364404481468533634986953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103152539308624711513315937 77364404481468533634986953)
  ·
    refine ⟨58023303361101400226240215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77364404481468533634986953 58023303361101400226240215)
    ·
      refine ⟨87034955041652100339360323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58023303361101400226240215 87034955041652100339360323)
      ·
        refine ⟨130552432562478150509040485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87034955041652100339360323 130552432562478150509040485)
        ·
          refine ⟨24478581105464653220445091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 130552432562478150509040485 24478581105464653220445091)
          ·
            refine ⟨36717871658196979830667637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24478581105464653220445091 36717871658196979830667637)
            ·
              refine ⟨3442300467955966859125091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36717871658196979830667637 3442300467955966859125091)
              ·
                refine ⟨5163450701933950288687637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3442300467955966859125091 5163450701933950288687637)
                ·
                  refine ⟨242036751653153919782233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5163450701933950288687637 242036751653153919782233)
                  ·
                    rfl

theorem cell23_4242284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 6].length) (baseStart_4242284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4242284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4242284 prefixEnd_4242284 := by exact prefixLift 4242284
  have htrace : WordTrace (prefixWord ++ tailWord_4242284) baseStart_4242284 baseEnd_4242284 := by
    simpa [prefixWord, tailWord_4242284, baseEnd_4242284] using wordTrace_append hprefix tailTrace_4242284
  have hstable : (prefixWord ++ tailWord_4242284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4242284).length < 2 ^ (prefixWord ++ tailWord_4242284).sum := by decide
  have hdescent : baseEnd_4242284 < baseStart_4242284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4242284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4242357 : List Nat := [1, 3, 3, 2, 1, 1, 1, 11]
def baseStart_4242357 : Nat := 118140960795 + 4242357 * 2 ^ 59
def prefixEnd_4242357 : Nat := 4983230072969 + 3 ^ 40 * 4242357 * 2
def baseEnd_4242357 : Nat := 80680305517265314534343

theorem tailTrace_4242357 : CollatzResearch.WordTrace tailWord_4242357 prefixEnd_4242357 80680305517265314534343 := by
  unfold tailWord_4242357
  simp only [CollatzResearch.WordTrace]
  refine ⟨154731471491672600737381325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103154314327781733824920883 154731471491672600737381325)
  ·
    refine ⟨58024301809377225276517997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154731471491672600737381325 58024301809377225276517997)
    ·
      refine ⟨21759113178516459478694249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58024301809377225276517997 21759113178516459478694249)
      ·
        refine ⟨16319334883887344609020687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21759113178516459478694249 16319334883887344609020687)
        ·
          refine ⟨24479002325831016913531031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16319334883887344609020687 24479002325831016913531031)
          ·
            refine ⟨36718503488746525370296547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24479002325831016913531031 36718503488746525370296547)
            ·
              refine ⟨55077755233119788055444821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36718503488746525370296547 55077755233119788055444821)
              ·
                refine ⟨80680305517265314534343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 55077755233119788055444821 80680305517265314534343)
                ·
                  rfl

theorem cell23_4242357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 11].length) (baseStart_4242357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4242357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4242357 prefixEnd_4242357 := by exact prefixLift 4242357
  have htrace : WordTrace (prefixWord ++ tailWord_4242357) baseStart_4242357 baseEnd_4242357 := by
    simpa [prefixWord, tailWord_4242357, baseEnd_4242357] using wordTrace_append hprefix tailTrace_4242357
  have hstable : (prefixWord ++ tailWord_4242357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4242357).length < 2 ^ (prefixWord ++ tailWord_4242357).sum := by decide
  have hdescent : baseEnd_4242357 < baseStart_4242357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4242357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4242427 : List Nat := [1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 5]
def baseStart_4242427 : Nat := 118140960795 + 4242427 * 2 ^ 59
def prefixEnd_4242427 : Nat := 4983230072969 + 3 ^ 40 * 4242427 * 2
def baseEnd_4242427 : Nat := 2178404192611978218551939

theorem tailTrace_4242427 : CollatzResearch.WordTrace tailWord_4242427 prefixEnd_4242427 2178404192611978218551939 := by
  unfold tailWord_4242427
  simp only [CollatzResearch.WordTrace]
  refine ⟨154734024601419002692429535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103156016400946001794953023 154734024601419002692429535)
  ·
    refine ⟨232101036902128504038644303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154734024601419002692429535 232101036902128504038644303)
    ·
      refine ⟨348151555353192756057966455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232101036902128504038644303 348151555353192756057966455)
      ·
        refine ⟨522227333029789134086949683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 348151555353192756057966455 522227333029789134086949683)
        ·
          refine ⟨783340999544683701130424525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 522227333029789134086949683 783340999544683701130424525)
          ·
            refine ⟨293752874829256387923909197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 783340999544683701130424525 293752874829256387923909197)
            ·
              refine ⟨110157328060971145471465949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 293752874829256387923909197 110157328060971145471465949)
              ·
                refine ⟨41308998022864179551799731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110157328060971145471465949 41308998022864179551799731)
                ·
                  refine ⟨61963497034296269327699597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41308998022864179551799731 61963497034296269327699597)
                  ·
                    refine ⟨23236311387861100997887349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61963497034296269327699597 23236311387861100997887349)
                    ·
                      refine ⟨2178404192611978218551939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23236311387861100997887349 2178404192611978218551939)
                      ·
                        rfl

theorem cell23_4242427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 5].length) (baseStart_4242427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4242427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4242427 prefixEnd_4242427 := by exact prefixLift 4242427
  have htrace : WordTrace (prefixWord ++ tailWord_4242427) baseStart_4242427 baseEnd_4242427 := by
    simpa [prefixWord, tailWord_4242427, baseEnd_4242427] using wordTrace_append hprefix tailTrace_4242427
  have hstable : (prefixWord ++ tailWord_4242427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4242427).length < 2 ^ (prefixWord ++ tailWord_4242427).sum := by decide
  have hdescent : baseEnd_4242427 < baseStart_4242427 := by decide
  rcases family_descends (prefixWord ++ tailWord_4242427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4242428 : List Nat := [2, 2, 2, 1, 2, 4, 1, 3, 1, 3, 2]
def baseStart_4242428 : Nat := 118140960795 + 4242428 * 2 ^ 59
def prefixEnd_4242428 : Nat := 4983230072969 + 3 ^ 40 * 4242428 * 2
def baseEnd_4242428 : Nat := 2178404706092632714639435

theorem tailTrace_4242428 : CollatzResearch.WordTrace tailWord_4242428 prefixEnd_4242428 2178404706092632714639435 := by
  unfold tailWord_4242428
  simp only [CollatzResearch.WordTrace]
  refine ⟨77367030537207689931607969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103156040716276919908810625 77367030537207689931607969)
  ·
    refine ⟨58025272902905767448705977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77367030537207689931607969 58025272902905767448705977)
    ·
      refine ⟨43518954677179325586529483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58025272902905767448705977 43518954677179325586529483)
      ·
        refine ⟨65278432015768988379794225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43518954677179325586529483 65278432015768988379794225)
        ·
          refine ⟨48958824011826741284845669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65278432015768988379794225 48958824011826741284845669)
          ·
            refine ⟨9179779502217513990908563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48958824011826741284845669 9179779502217513990908563)
            ·
              refine ⟨13769669253326270986362845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9179779502217513990908563 13769669253326270986362845)
              ·
                refine ⟨5163625969997351619886067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13769669253326270986362845 5163625969997351619886067)
                ·
                  refine ⟨7745438954996027429829101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5163625969997351619886067 7745438954996027429829101)
                  ·
                    refine ⟨2904539608123510286185913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7745438954996027429829101 2904539608123510286185913)
                    ·
                      refine ⟨2178404706092632714639435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2904539608123510286185913 2178404706092632714639435)
                      ·
                        rfl

theorem cell23_4242428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 3, 1, 3, 2].length) (baseStart_4242428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4242428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4242428 prefixEnd_4242428 := by exact prefixLift 4242428
  have htrace : WordTrace (prefixWord ++ tailWord_4242428) baseStart_4242428 baseEnd_4242428 := by
    simpa [prefixWord, tailWord_4242428, baseEnd_4242428] using wordTrace_append hprefix tailTrace_4242428
  have hstable : (prefixWord ++ tailWord_4242428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4242428).length < 2 ^ (prefixWord ++ tailWord_4242428).sum := by decide
  have hdescent : baseEnd_4242428 < baseStart_4242428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4242428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4242504 : List Nat := [2, 1, 3, 1, 1, 1, 5, 1, 1, 2, 5]
def baseStart_4242504 : Nat := 118140960795 + 4242504 * 2 ^ 59
def prefixEnd_4242504 : Nat := 4983230072969 + 3 ^ 40 * 4242504 * 2
def baseEnd_4242504 : Nat := 2178443730622374417289085

theorem tailTrace_4242504 : CollatzResearch.WordTrace tailWord_4242504 prefixEnd_4242504 2178443730622374417289085 := by
  unfold tailWord_4242504
  simp only [CollatzResearch.WordTrace]
  refine ⟨77368416511070022421491283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103157888681426696561988377 77368416511070022421491283)
  ·
    refine ⟨116052624766605033632236925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77368416511070022421491283 116052624766605033632236925)
    ·
      refine ⟨43519734287476887612088847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116052624766605033632236925 43519734287476887612088847)
      ·
        refine ⟨65279601431215331418133271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43519734287476887612088847 65279601431215331418133271)
        ·
          refine ⟨97919402146822997127199907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65279601431215331418133271 97919402146822997127199907)
          ·
            refine ⟨146879103220234495690799861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97919402146822997127199907 146879103220234495690799861)
            ·
              refine ⟨13769915926896983971012487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 146879103220234495690799861 13769915926896983971012487)
              ·
                refine ⟨20654873890345475956518731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13769915926896983971012487 20654873890345475956518731)
                ·
                  refine ⟨30982310835518213934778097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20654873890345475956518731 30982310835518213934778097)
                  ·
                    refine ⟨23236733126638660451083573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30982310835518213934778097 23236733126638660451083573)
                    ·
                      refine ⟨2178443730622374417289085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23236733126638660451083573 2178443730622374417289085)
                      ·
                        rfl

theorem cell23_4242504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_4242504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4242504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4242504 prefixEnd_4242504 := by exact prefixLift 4242504
  have htrace : WordTrace (prefixWord ++ tailWord_4242504) baseStart_4242504 baseEnd_4242504 := by
    simpa [prefixWord, tailWord_4242504, baseEnd_4242504] using wordTrace_append hprefix tailTrace_4242504
  have hstable : (prefixWord ++ tailWord_4242504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4242504).length < 2 ^ (prefixWord ++ tailWord_4242504).sum := by decide
  have hdescent : baseEnd_4242504 < baseStart_4242504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4242504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4242509 : List Nat := [1, 6, 1, 1, 1, 4, 2, 1, 2, 2, 2]
def baseStart_4242509 : Nat := 118140960795 + 4242509 * 2 ^ 59
def prefixEnd_4242509 : Nat := 4983230072969 + 3 ^ 40 * 4242509 * 2
def baseEnd_4242509 : Nat := 2178446298025646897726563

theorem tailTrace_4242509 : CollatzResearch.WordTrace tailWord_4242509 prefixEnd_4242509 2178446298025646897726563 := by
  unfold tailWord_4242509
  simp only [CollatzResearch.WordTrace]
  refine ⟨154737015387121930696914581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103158010258081287131276387 154737015387121930696914581)
  ·
    refine ⟨7253297596271340501417871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 154737015387121930696914581 7253297596271340501417871)
    ·
      refine ⟨10879946394407010752126807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7253297596271340501417871 10879946394407010752126807)
      ·
        refine ⟨16319919591610516128190211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10879946394407010752126807 16319919591610516128190211)
        ·
          refine ⟨24479879387415774192285317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16319919591610516128190211 24479879387415774192285317)
          ·
            refine ⟨4589977385140457661053497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24479879387415774192285317 4589977385140457661053497)
            ·
              refine ⟨3442483038855343245790123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4589977385140457661053497 3442483038855343245790123)
              ·
                refine ⟨5163724558283014868685185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3442483038855343245790123 5163724558283014868685185)
                ·
                  refine ⟨3872793418712261151513889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5163724558283014868685185 3872793418712261151513889)
                  ·
                    refine ⟨2904595064034195863635417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3872793418712261151513889 2904595064034195863635417)
                    ·
                      refine ⟨2178446298025646897726563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2904595064034195863635417 2178446298025646897726563)
                      ·
                        rfl

theorem cell23_4242509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_4242509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4242509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4242509 prefixEnd_4242509 := by exact prefixLift 4242509
  have htrace : WordTrace (prefixWord ++ tailWord_4242509) baseStart_4242509 baseEnd_4242509 := by
    simpa [prefixWord, tailWord_4242509, baseEnd_4242509] using wordTrace_append hprefix tailTrace_4242509
  have hstable : (prefixWord ++ tailWord_4242509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4242509).length < 2 ^ (prefixWord ++ tailWord_4242509).sum := by decide
  have hdescent : baseEnd_4242509 < baseStart_4242509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4242509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4242531 : List Nat := [1, 1, 1, 5, 1, 1, 1, 2, 4, 4, 2]
def baseStart_4242531 : Nat := 118140960795 + 4242531 * 2 ^ 59
def prefixEnd_4242531 : Nat := 4983230072969 + 3 ^ 40 * 4242531 * 2
def baseEnd_4242531 : Nat := 2178457594600045811651461

theorem tailTrace_4242531 : CollatzResearch.WordTrace tailWord_4242531 prefixEnd_4242531 2178457594600045811651461 := by
  unfold tailWord_4242531
  simp only [CollatzResearch.WordTrace]
  refine ⟨154737817793042228454215447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103158545195361485636143631 154737817793042228454215447)
  ·
    refine ⟨232106726689563342681323171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154737817793042228454215447 232106726689563342681323171)
    ·
      refine ⟨348160090034345014021984757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232106726689563342681323171 348160090034345014021984757)
      ·
        refine ⟨32640008440719845064561071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 348160090034345014021984757 32640008440719845064561071)
        ·
          refine ⟨48960012661079767596841607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32640008440719845064561071 48960012661079767596841607)
          ·
            refine ⟨73440018991619651395262411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48960012661079767596841607 73440018991619651395262411)
            ·
              refine ⟨110160028487429477092893617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73440018991619651395262411 110160028487429477092893617)
              ·
                refine ⟨82620021365572107819670213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110160028487429477092893617 82620021365572107819670213)
                ·
                  refine ⟨15491254006044770216188165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82620021365572107819670213 15491254006044770216188165)
                  ·
                    refine ⟨2904610126133394415535281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15491254006044770216188165 2904610126133394415535281)
                    ·
                      refine ⟨2178457594600045811651461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2904610126133394415535281 2178457594600045811651461)
                      ·
                        rfl

theorem cell23_4242531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 4, 2].length) (baseStart_4242531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4242531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4242531 prefixEnd_4242531 := by exact prefixLift 4242531
  have htrace : WordTrace (prefixWord ++ tailWord_4242531) baseStart_4242531 baseEnd_4242531 := by
    simpa [prefixWord, tailWord_4242531, baseEnd_4242531] using wordTrace_append hprefix tailTrace_4242531
  have hstable : (prefixWord ++ tailWord_4242531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4242531).length < 2 ^ (prefixWord ++ tailWord_4242531).sum := by decide
  have hdescent : baseEnd_4242531 < baseStart_4242531 := by decide
  rcases family_descends (prefixWord ++ tailWord_4242531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4242544 : List Nat := [2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 6]
def baseStart_4242544 : Nat := 118140960795 + 4242544 * 2 ^ 59
def prefixEnd_4242544 : Nat := 4983230072969 + 3 ^ 40 * 4242544 * 2
def baseEnd_4242544 : Nat := 2178464269848554260788901

theorem tailTrace_4242544 : CollatzResearch.WordTrace tailWord_4242544 prefixEnd_4242544 2178464269848554260788901 := by
  unfold tailWord_4242544
  simp only [CollatzResearch.WordTrace]
  refine ⟨77369145970997565837219343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103158861294663421116292457 77369145970997565837219343)
  ·
    refine ⟨116053718956496348755829015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77369145970997565837219343 116053718956496348755829015)
    ·
      refine ⟨174080578434744523133743523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116053718956496348755829015 174080578434744523133743523)
      ·
        refine ⟨261120867652116784700615285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174080578434744523133743523 261120867652116784700615285)
        ·
          refine ⟨24480081342385948565682683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 261120867652116784700615285 24480081342385948565682683)
          ·
            refine ⟨36720122013578922848524025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24480081342385948565682683 36720122013578922848524025)
            ·
              refine ⟨27540091510184192136393019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36720122013578922848524025 27540091510184192136393019)
              ·
                refine ⟨41310137265276288204589529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27540091510184192136393019 41310137265276288204589529)
                ·
                  refine ⟨30982602948957216153442147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41310137265276288204589529 30982602948957216153442147)
                  ·
                    refine ⟨46473904423435824230163221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30982602948957216153442147 46473904423435824230163221)
                    ·
                      refine ⟨2178464269848554260788901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46473904423435824230163221 2178464269848554260788901)
                      ·
                        rfl

theorem cell23_4242544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 6].length) (baseStart_4242544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4242544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4242544 prefixEnd_4242544 := by exact prefixLift 4242544
  have htrace : WordTrace (prefixWord ++ tailWord_4242544) baseStart_4242544 baseEnd_4242544 := by
    simpa [prefixWord, tailWord_4242544, baseEnd_4242544] using wordTrace_append hprefix tailTrace_4242544
  have hstable : (prefixWord ++ tailWord_4242544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4242544).length < 2 ^ (prefixWord ++ tailWord_4242544).sum := by decide
  have hdescent : baseEnd_4242544 < baseStart_4242544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4242544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4242549 : List Nat := [1, 3, 4, 3, 2, 1, 2, 2, 5]
def baseStart_4242549 : Nat := 118140960795 + 4242549 * 2 ^ 59
def prefixEnd_4242549 : Nat := 4983230072969 + 3 ^ 40 * 4242549 * 2
def baseEnd_4242549 : Nat := 242051870805758526802931

theorem tailTrace_4242549 : CollatzResearch.WordTrace tailWord_4242549 prefixEnd_4242549 242051870805758526802931 := by
  unfold tailWord_4242549
  simp only [CollatzResearch.WordTrace]
  refine ⟨154738474306977017528370701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103158982871318011685580467 154738474306977017528370701)
  ·
    refine ⟨58026927865116381573139013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154738474306977017528370701 58026927865116381573139013)
    ·
      refine ⟨10880048974709321544963565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58026927865116381573139013 10880048974709321544963565)
      ·
        refine ⟨4080018365515995579361337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10880048974709321544963565 4080018365515995579361337)
        ·
          refine ⟨3060013774136996684521003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4080018365515995579361337 3060013774136996684521003)
          ·
            refine ⟨4590020661205495026781505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3060013774136996684521003 4590020661205495026781505)
            ·
              refine ⟨3442515495904121270086129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4590020661205495026781505 3442515495904121270086129)
              ·
                refine ⟨2581886621928090952564597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3442515495904121270086129 2581886621928090952564597)
                ·
                  refine ⟨242051870805758526802931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2581886621928090952564597 242051870805758526802931)
                  ·
                    rfl

theorem cell23_4242549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 2, 5].length) (baseStart_4242549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4242549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4242549 prefixEnd_4242549 := by exact prefixLift 4242549
  have htrace : WordTrace (prefixWord ++ tailWord_4242549) baseStart_4242549 baseEnd_4242549 := by
    simpa [prefixWord, tailWord_4242549, baseEnd_4242549] using wordTrace_append hprefix tailTrace_4242549
  have hstable : (prefixWord ++ tailWord_4242549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4242549).length < 2 ^ (prefixWord ++ tailWord_4242549).sum := by decide
  have hdescent : baseEnd_4242549 < baseStart_4242549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4242549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4242551 : List Nat := [1, 1, 3, 1, 1, 4, 1, 4, 2, 2, 3]
def baseStart_4242551 : Nat := 118140960795 + 4242551 * 2 ^ 59
def prefixEnd_4242551 : Nat := 4983230072969 + 3 ^ 40 * 4242551 * 2
def baseEnd_4242551 : Nat := 2178467864213135733401369

theorem tailTrace_4242551 : CollatzResearch.WordTrace tailWord_4242551 prefixEnd_4242551 2178467864213135733401369 := by
  unfold tailWord_4242551
  simp only [CollatzResearch.WordTrace]
  refine ⟨154738547252969771869943507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103159031501979847913295671 154738547252969771869943507)
  ·
    refine ⟨232107820879454657804915261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154738547252969771869943507 232107820879454657804915261)
    ·
      refine ⟨87040432829795496676843223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 232107820879454657804915261 87040432829795496676843223)
      ·
        refine ⟨130560649244693245015264835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87040432829795496676843223 130560649244693245015264835)
        ·
          refine ⟨195840973867039867522897253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130560649244693245015264835 195840973867039867522897253)
          ·
            refine ⟨36720182600069975160543235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 195840973867039867522897253 36720182600069975160543235)
            ·
              refine ⟨55080273900104962740814853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36720182600069975160543235 55080273900104962740814853)
              ·
                refine ⟨10327551356269680513902785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55080273900104962740814853 10327551356269680513902785)
                ·
                  refine ⟨7745663517202260385427089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10327551356269680513902785 7745663517202260385427089)
                  ·
                    refine ⟨5809247637901695289070317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7745663517202260385427089 5809247637901695289070317)
                    ·
                      refine ⟨2178467864213135733401369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5809247637901695289070317 2178467864213135733401369)
                      ·
                        rfl

theorem cell23_4242551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 2, 2, 3].length) (baseStart_4242551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4242551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4242551 prefixEnd_4242551 := by exact prefixLift 4242551
  have htrace : WordTrace (prefixWord ++ tailWord_4242551) baseStart_4242551 baseEnd_4242551 := by
    simpa [prefixWord, tailWord_4242551, baseEnd_4242551] using wordTrace_append hprefix tailTrace_4242551
  have hstable : (prefixWord ++ tailWord_4242551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4242551).length < 2 ^ (prefixWord ++ tailWord_4242551).sum := by decide
  have hdescent : baseEnd_4242551 < baseStart_4242551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4242551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4242605 : List Nat := [1, 5, 2, 1, 3, 2, 1, 2, 6]
def baseStart_4242605 : Nat := 118140960795 + 4242605 * 2 ^ 59
def prefixEnd_4242605 : Nat := 4983230072969 + 3 ^ 40 * 4242605 * 2
def baseEnd_4242605 : Nat := 242055065796497613569569

theorem tailTrace_4242605 : CollatzResearch.WordTrace tailWord_4242605 prefixEnd_4242605 242055065796497613569569 := by
  unfold tailWord_4242605
  simp only [CollatzResearch.WordTrace]
  refine ⟨154740516794774139092409269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103160344529849426061606179 154740516794774139092409269)
  ·
    refine ⟨14506923449510075539913369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 154740516794774139092409269 14506923449510075539913369)
    ·
      refine ⟨10880192587132556654935027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14506923449510075539913369 10880192587132556654935027)
      ·
        refine ⟨16320288880698834982402541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10880192587132556654935027 16320288880698834982402541)
        ·
          refine ⟨6120108330262063118400953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16320288880698834982402541 6120108330262063118400953)
          ·
            refine ⟨4590081247696547338800715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6120108330262063118400953 4590081247696547338800715)
            ·
              refine ⟨6885121871544821008201073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4590081247696547338800715 6885121871544821008201073)
              ·
                refine ⟨5163841403658615756150805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6885121871544821008201073 5163841403658615756150805)
                ·
                  refine ⟨242055065796497613569569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5163841403658615756150805 242055065796497613569569)
                  ·
                    rfl

theorem cell23_4242605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 2, 6].length) (baseStart_4242605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4242605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4242605 prefixEnd_4242605 := by exact prefixLift 4242605
  have htrace : WordTrace (prefixWord ++ tailWord_4242605) baseStart_4242605 baseEnd_4242605 := by
    simpa [prefixWord, tailWord_4242605, baseEnd_4242605] using wordTrace_append hprefix tailTrace_4242605
  have hstable : (prefixWord ++ tailWord_4242605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4242605).length < 2 ^ (prefixWord ++ tailWord_4242605).sum := by decide
  have hdescent : baseEnd_4242605 < baseStart_4242605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4242605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4242615 : List Nat := [1, 1, 3, 1, 4, 1, 1, 6, 1, 1, 3]
def baseStart_4242615 : Nat := 118140960795 + 4242615 * 2 ^ 59
def prefixEnd_4242615 : Nat := 4983230072969 + 3 ^ 40 * 4242615 * 2
def baseEnd_4242615 : Nat := 2178500726975023483001075

theorem tailTrace_4242615 : CollatzResearch.WordTrace tailWord_4242615 prefixEnd_4242615 2178500726975023483001075 := by
  unfold tailWord_4242615
  simp only [CollatzResearch.WordTrace]
  refine ⟨154740881524737910800273299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103160587683158607200182199 154740881524737910800273299)
  ·
    refine ⟨232111322287106866200409949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154740881524737910800273299 232111322287106866200409949)
    ·
      refine ⟨87041745857665074825153731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 232111322287106866200409949 87041745857665074825153731)
      ·
        refine ⟨130562618786497612237730597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87041745857665074825153731 130562618786497612237730597)
        ·
          refine ⟨24480491022468302294574487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 130562618786497612237730597 24480491022468302294574487)
          ·
            refine ⟨36720736533702453441861731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24480491022468302294574487 36720736533702453441861731)
            ·
              refine ⟨55081104800553680162792597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36720736533702453441861731 55081104800553680162792597)
              ·
                refine ⟨2581926787525953757630903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 55081104800553680162792597 2581926787525953757630903)
                ·
                  refine ⟨3872890181288930636446355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2581926787525953757630903 3872890181288930636446355)
                  ·
                    refine ⟨5809335271933395954669533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3872890181288930636446355 5809335271933395954669533)
                    ·
                      refine ⟨2178500726975023483001075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5809335271933395954669533 2178500726975023483001075)
                      ·
                        rfl

theorem cell23_4242615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 6, 1, 1, 3].length) (baseStart_4242615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4242615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4242615 prefixEnd_4242615 := by exact prefixLift 4242615
  have htrace : WordTrace (prefixWord ++ tailWord_4242615) baseStart_4242615 baseEnd_4242615 := by
    simpa [prefixWord, tailWord_4242615, baseEnd_4242615] using wordTrace_append hprefix tailTrace_4242615
  have hstable : (prefixWord ++ tailWord_4242615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4242615).length < 2 ^ (prefixWord ++ tailWord_4242615).sum := by decide
  have hdescent : baseEnd_4242615 < baseStart_4242615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4242615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4242621 : List Nat := [1, 4, 1, 2, 1, 1, 2, 1, 5, 1, 4]
def baseStart_4242621 : Nat := 118140960795 + 4242621 * 2 ^ 59
def prefixEnd_4242621 : Nat := 4983230072969 + 3 ^ 40 * 4242621 * 2
def baseEnd_4242621 : Nat := 2178503807858950459526047

theorem tailTrace_4242621 : CollatzResearch.WordTrace tailWord_4242621 prefixEnd_4242621 2178503807858950459526047 := by
  unfold tailWord_4242621
  simp only [CollatzResearch.WordTrace]
  refine ⟨154741100362716173824991717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103160733575144115883327811 154741100362716173824991717)
  ·
    refine ⟨29013956318009282592185947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 154741100362716173824991717 29013956318009282592185947)
    ·
      refine ⟨43520934477013923888278921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29013956318009282592185947 43520934477013923888278921)
      ·
        refine ⟨32640700857760442916209191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43520934477013923888278921 32640700857760442916209191)
        ·
          refine ⟨48961051286640664374313787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32640700857760442916209191 48961051286640664374313787)
          ·
            refine ⟨73441576929960996561470681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48961051286640664374313787 73441576929960996561470681)
            ·
              refine ⟨55081182697470747421103011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73441576929960996561470681 55081182697470747421103011)
              ·
                refine ⟨82621774046206121131654517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55081182697470747421103011 82621774046206121131654517)
                ·
                  refine ⟨7745791316831823856092611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 82621774046206121131654517 7745791316831823856092611)
                  ·
                    refine ⟨11618686975247735784138917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7745791316831823856092611 11618686975247735784138917)
                    ·
                      refine ⟨2178503807858950459526047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11618686975247735784138917 2178503807858950459526047)
                      ·
                        rfl

theorem cell23_4242621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_4242621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4242621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4242621 prefixEnd_4242621 := by exact prefixLift 4242621
  have htrace : WordTrace (prefixWord ++ tailWord_4242621) baseStart_4242621 baseEnd_4242621 := by
    simpa [prefixWord, tailWord_4242621, baseEnd_4242621] using wordTrace_append hprefix tailTrace_4242621
  have hstable : (prefixWord ++ tailWord_4242621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4242621).length < 2 ^ (prefixWord ++ tailWord_4242621).sum := by decide
  have hdescent : baseEnd_4242621 < baseStart_4242621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4242621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4242625 : List Nat := [1, 2, 6, 1, 1, 1, 1, 2, 1, 5, 2]
def baseStart_4242625 : Nat := 118140960795 + 4242625 * 2 ^ 59
def prefixEnd_4242625 : Nat := 4983230072969 + 3 ^ 40 * 4242625 * 2
def baseEnd_4242625 : Nat := 2178505861781568443876029

theorem tailTrace_4242625 : CollatzResearch.WordTrace tailWord_4242625 prefixEnd_4242625 2178505861781568443876029 := by
  unfold tailWord_4242625
  simp only [CollatzResearch.WordTrace]
  refine ⟨154741246254701682508137329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103160830836467788338758219 154741246254701682508137329)
  ·
    refine ⟨116055934691026261881102997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154741246254701682508137329 116055934691026261881102997)
    ·
      refine ⟨5440121938641856025676703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 116055934691026261881102997 5440121938641856025676703)
      ·
        refine ⟨8160182907962784038515055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5440121938641856025676703 8160182907962784038515055)
        ·
          refine ⟨12240274361944176057772583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8160182907962784038515055 12240274361944176057772583)
          ·
            refine ⟨18360411542916264086658875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12240274361944176057772583 18360411542916264086658875)
            ·
              refine ⟨27540617314374396129988313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18360411542916264086658875 27540617314374396129988313)
              ·
                refine ⟨20655462985780797097491235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27540617314374396129988313 20655462985780797097491235)
                ·
                  refine ⟨30983194478671195646236853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20655462985780797097491235 30983194478671195646236853)
                  ·
                    refine ⟨2904674482375424591834705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30983194478671195646236853 2904674482375424591834705)
                    ·
                      refine ⟨2178505861781568443876029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2904674482375424591834705 2178505861781568443876029)
                      ·
                        rfl

theorem cell23_4242625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_4242625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4242625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4242625 prefixEnd_4242625 := by exact prefixLift 4242625
  have htrace : WordTrace (prefixWord ++ tailWord_4242625) baseStart_4242625 baseEnd_4242625 := by
    simpa [prefixWord, tailWord_4242625, baseEnd_4242625] using wordTrace_append hprefix tailTrace_4242625
  have hstable : (prefixWord ++ tailWord_4242625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4242625).length < 2 ^ (prefixWord ++ tailWord_4242625).sum := by decide
  have hdescent : baseEnd_4242625 < baseStart_4242625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4242625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4242692 : List Nat := [2, 3, 2, 2, 2, 3, 1, 2, 1, 2, 3]
def baseStart_4242692 : Nat := 118140960795 + 4242692 * 2 ^ 59
def prefixEnd_4242692 : Nat := 4983230072969 + 3 ^ 40 * 4242692 * 2
def baseEnd_4242692 : Nat := 2178540264985419681738221

theorem tailTrace_4242692 : CollatzResearch.WordTrace tailWord_4242692 prefixEnd_4242692 2178540264985419681738221 := by
  unfold tailWord_4242692
  simp only [CollatzResearch.WordTrace]
  refine ⟨77371844972729476475413165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103162459963639301967217553 77371844972729476475413165)
  ·
    refine ⟨29014441864773553678279937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77371844972729476475413165 29014441864773553678279937)
    ·
      refine ⟨21760831398580165258709953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29014441864773553678279937 21760831398580165258709953)
      ·
        refine ⟨16320623548935123944032465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21760831398580165258709953 16320623548935123944032465)
        ·
          refine ⟨12240467661701342958024349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16320623548935123944032465 12240467661701342958024349)
          ·
            refine ⟨4590175373138003609259131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12240467661701342958024349 4590175373138003609259131)
            ·
              refine ⟨6885263059707005413888697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4590175373138003609259131 6885263059707005413888697)
              ·
                refine ⟨5163947294780254060416523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6885263059707005413888697 5163947294780254060416523)
                ·
                  refine ⟨7745920942170381090624785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5163947294780254060416523 7745920942170381090624785)
                  ·
                    refine ⟨5809440706627785817968589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7745920942170381090624785 5809440706627785817968589)
                    ·
                      refine ⟨2178540264985419681738221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5809440706627785817968589 2178540264985419681738221)
                      ·
                        rfl

theorem cell23_4242692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_4242692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4242692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4242692 prefixEnd_4242692 := by exact prefixLift 4242692
  have htrace : WordTrace (prefixWord ++ tailWord_4242692) baseStart_4242692 baseEnd_4242692 := by
    simpa [prefixWord, tailWord_4242692, baseEnd_4242692] using wordTrace_append hprefix tailTrace_4242692
  have hstable : (prefixWord ++ tailWord_4242692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4242692).length < 2 ^ (prefixWord ++ tailWord_4242692).sum := by decide
  have hdescent : baseEnd_4242692 < baseStart_4242692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4242692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4242721 : List Nat := [1, 2, 3, 2, 1, 1, 1, 4, 2, 6]
def baseStart_4242721 : Nat := 118140960795 + 4242721 * 2 ^ 59
def prefixEnd_4242721 : Nat := 4983230072969 + 3 ^ 40 * 4242721 * 2
def baseEnd_4242721 : Nat := 726185051974800022758529

theorem tailTrace_4242721 : CollatzResearch.WordTrace tailWord_4242721 prefixEnd_4242721 726185051974800022758529 := by
  unfold tailWord_4242721
  simp only [CollatzResearch.WordTrace]
  refine ⟨154744747662353890903632017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103163165108235927269088011 154744747662353890903632017)
  ·
    refine ⟨116058560746765418177724013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154744747662353890903632017 116058560746765418177724013)
    ·
      refine ⟨43521960280037031816646505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116058560746765418177724013 43521960280037031816646505)
      ·
        refine ⟨32641470210027773862484879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43521960280037031816646505 32641470210027773862484879)
        ·
          refine ⟨48962205315041660793727319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32641470210027773862484879 48962205315041660793727319)
          ·
            refine ⟨73443307972562491190590979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48962205315041660793727319 73443307972562491190590979)
            ·
              refine ⟨110164961958843736785886469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73443307972562491190590979 110164961958843736785886469)
              ·
                refine ⟨20655930367283200647353713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 110164961958843736785886469 20655930367283200647353713)
                ·
                  refine ⟨15491947775462400485515285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20655930367283200647353713 15491947775462400485515285)
                  ·
                    refine ⟨726185051974800022758529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15491947775462400485515285 726185051974800022758529)
                    ·
                      rfl

theorem cell23_4242721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 6].length) (baseStart_4242721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4242721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4242721 prefixEnd_4242721 := by exact prefixLift 4242721
  have htrace : WordTrace (prefixWord ++ tailWord_4242721) baseStart_4242721 baseEnd_4242721 := by
    simpa [prefixWord, tailWord_4242721, baseEnd_4242721] using wordTrace_append hprefix tailTrace_4242721
  have hstable : (prefixWord ++ tailWord_4242721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4242721).length < 2 ^ (prefixWord ++ tailWord_4242721).sum := by decide
  have hdescent : baseEnd_4242721 < baseStart_4242721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4242721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4242728 : List Nat := [2, 1, 5, 1, 2, 1, 1, 1, 2, 3, 4]
def baseStart_4242728 : Nat := 118140960795 + 4242728 * 2 ^ 59
def prefixEnd_4242728 : Nat := 4983230072969 + 3 ^ 40 * 4242728 * 2
def baseEnd_4242728 : Nat := 2178558750288981540888055

theorem tailTrace_4242728 : CollatzResearch.WordTrace tailWord_4242728 prefixEnd_4242728 2178558750288981540888055 := by
  unfold tailWord_4242728
  simp only [CollatzResearch.WordTrace]
  refine ⟨77372501486664265549568419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103163335315552354066091225 77372501486664265549568419)
  ·
    refine ⟨116058752229996398324352629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77372501486664265549568419 116058752229996398324352629)
    ·
      refine ⟨10880508021562162342908059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 116058752229996398324352629 10880508021562162342908059)
      ·
        refine ⟨16320762032343243514362089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10880508021562162342908059 16320762032343243514362089)
        ·
          refine ⟨12240571524257432635771567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16320762032343243514362089 12240571524257432635771567)
          ·
            refine ⟨18360857286386148953657351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12240571524257432635771567 18360857286386148953657351)
            ·
              refine ⟨27541285929579223430486027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18360857286386148953657351 27541285929579223430486027)
              ·
                refine ⟨41311928894368835145729041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27541285929579223430486027 41311928894368835145729041)
                ·
                  refine ⟨30983946670776626359296781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41311928894368835145729041 30983946670776626359296781)
                  ·
                    refine ⟨11618980001541234884736293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30983946670776626359296781 11618980001541234884736293)
                    ·
                      refine ⟨2178558750288981540888055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11618980001541234884736293 2178558750288981540888055)
                      ·
                        rfl

theorem cell23_4242728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_4242728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4242728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4242728 prefixEnd_4242728 := by exact prefixLift 4242728
  have htrace : WordTrace (prefixWord ++ tailWord_4242728) baseStart_4242728 baseEnd_4242728 := by
    simpa [prefixWord, tailWord_4242728, baseEnd_4242728] using wordTrace_append hprefix tailTrace_4242728
  have hstable : (prefixWord ++ tailWord_4242728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4242728).length < 2 ^ (prefixWord ++ tailWord_4242728).sum := by decide
  have hdescent : baseEnd_4242728 < baseStart_4242728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4242728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4242738 : List Nat := [3, 2, 1, 1, 4, 2, 1, 1, 2, 6]
def baseStart_4242738 : Nat := 118140960795 + 4242738 * 2 ^ 59
def prefixEnd_4242738 : Nat := 4983230072969 + 3 ^ 40 * 4242738 * 2
def baseEnd_4242738 : Nat := 726187961698508833921003

theorem tailTrace_4242738 : CollatzResearch.WordTrace tailWord_4242738 prefixEnd_4242738 726187961698508833921003 := by
  unfold tailWord_4242738
  simp only [CollatzResearch.WordTrace]
  refine ⟨38686341925823075701750217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103163578468861535204667245 38686341925823075701750217)
  ·
    refine ⟨29014756444367306776312663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38686341925823075701750217 29014756444367306776312663)
    ·
      refine ⟨43522134666550960164468995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29014756444367306776312663 43522134666550960164468995)
      ·
        refine ⟨65283201999826440246703493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43522134666550960164468995 65283201999826440246703493)
        ·
          refine ⟨12240600374967457546256905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65283201999826440246703493 12240600374967457546256905)
          ·
            refine ⟨9180450281225593159692679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12240600374967457546256905 9180450281225593159692679)
            ·
              refine ⟨13770675421838389739539019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9180450281225593159692679 13770675421838389739539019)
              ·
                refine ⟨20656013132757584609308529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13770675421838389739539019 20656013132757584609308529)
                ·
                  refine ⟨15492009849568188456981397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20656013132757584609308529 15492009849568188456981397)
                  ·
                    refine ⟨726187961698508833921003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15492009849568188456981397 726187961698508833921003)
                    ·
                      rfl

theorem cell23_4242738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 2, 6].length) (baseStart_4242738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4242738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4242738 prefixEnd_4242738 := by exact prefixLift 4242738
  have htrace : WordTrace (prefixWord ++ tailWord_4242738) baseStart_4242738 baseEnd_4242738 := by
    simpa [prefixWord, tailWord_4242738, baseEnd_4242738] using wordTrace_append hprefix tailTrace_4242738
  have hstable : (prefixWord ++ tailWord_4242738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4242738).length < 2 ^ (prefixWord ++ tailWord_4242738).sum := by decide
  have hdescent : baseEnd_4242738 < baseStart_4242738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4242738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4242751 : List Nat := [1, 1, 2, 2, 4, 2, 1, 1, 9]
def baseStart_4242751 : Nat := 118140960795 + 4242751 * 2 ^ 59
def prefixEnd_4242751 : Nat := 4983230072969 + 3 ^ 40 * 4242751 * 2
def baseEnd_4242751 : Nat := 242063395593781661211161

theorem tailTrace_4242751 : CollatzResearch.WordTrace tailWord_4242751 prefixEnd_4242751 242063395593781661211161 := by
  unfold tailWord_4242751
  simp only [CollatzResearch.WordTrace]
  refine ⟨154745841852245206027224107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103163894568163470684816071 154745841852245206027224107)
  ·
    refine ⟨232118762778367809040836161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154745841852245206027224107 232118762778367809040836161)
    ·
      refine ⟨174089072083775856780627121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232118762778367809040836161 174089072083775856780627121)
      ·
        refine ⟨130566804062831892585470341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174089072083775856780627121 130566804062831892585470341)
        ·
          refine ⟨24481275761780979859775689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 130566804062831892585470341 24481275761780979859775689)
          ·
            refine ⟨18360956821335734894831767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24481275761780979859775689 18360956821335734894831767)
            ·
              refine ⟨27541435232003602342247651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18360956821335734894831767 27541435232003602342247651)
              ·
                refine ⟨41312152848005403513371477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27541435232003602342247651 41312152848005403513371477)
                ·
                  refine ⟨242063395593781661211161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 41312152848005403513371477 242063395593781661211161)
                  ·
                    rfl

theorem cell23_4242751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 9].length) (baseStart_4242751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4242751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4242751 prefixEnd_4242751 := by exact prefixLift 4242751
  have htrace : WordTrace (prefixWord ++ tailWord_4242751) baseStart_4242751 baseEnd_4242751 := by
    simpa [prefixWord, tailWord_4242751, baseEnd_4242751] using wordTrace_append hprefix tailTrace_4242751
  have hstable : (prefixWord ++ tailWord_4242751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4242751).length < 2 ^ (prefixWord ++ tailWord_4242751).sum := by decide
  have hdescent : baseEnd_4242751 < baseStart_4242751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4242751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4242778 : List Nat := [3, 1, 1, 2, 1, 2, 3, 2, 2, 3, 3]
def baseStart_4242778 : Nat := 118140960795 + 4242778 * 2 ^ 59
def prefixEnd_4242778 : Nat := 4983230072969 + 3 ^ 40 * 4242778 * 2
def baseEnd_4242778 : Nat := 2178584424321706345262825

theorem tailTrace_4242778 : CollatzResearch.WordTrace tailWord_4242778 prefixEnd_4242778 2178584424321706345262825 := by
  unfold tailWord_4242778
  simp only [CollatzResearch.WordTrace]
  refine ⟨38686706655786847409614247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103164551082098259758971325 38686706655786847409614247)
  ·
    refine ⟨58030059983680271114421371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38686706655786847409614247 58030059983680271114421371)
    ·
      refine ⟨87045089975520406671632057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58030059983680271114421371 87045089975520406671632057)
      ·
        refine ⟨65283817481640305003724043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87045089975520406671632057 65283817481640305003724043)
        ·
          refine ⟨97925726222460457505586065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65283817481640305003724043 97925726222460457505586065)
          ·
            refine ⟨73444294666845343129189549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97925726222460457505586065 73444294666845343129189549)
            ·
              refine ⟨27541610500067003673446081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73444294666845343129189549 27541610500067003673446081)
              ·
                refine ⟨20656207875050252755084561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27541610500067003673446081 20656207875050252755084561)
                ·
                  refine ⟨15492155906287689566313421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20656207875050252755084561 15492155906287689566313421)
                  ·
                    refine ⟨5809558464857883587367533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15492155906287689566313421 5809558464857883587367533)
                    ·
                      refine ⟨2178584424321706345262825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5809558464857883587367533 2178584424321706345262825)
                      ·
                        rfl

theorem cell23_4242778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 2, 3, 3].length) (baseStart_4242778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4242778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4242778 prefixEnd_4242778 := by exact prefixLift 4242778
  have htrace : WordTrace (prefixWord ++ tailWord_4242778) baseStart_4242778 baseEnd_4242778 := by
    simpa [prefixWord, tailWord_4242778, baseEnd_4242778] using wordTrace_append hprefix tailTrace_4242778
  have hstable : (prefixWord ++ tailWord_4242778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4242778).length < 2 ^ (prefixWord ++ tailWord_4242778).sum := by decide
  have hdescent : baseEnd_4242778 < baseStart_4242778 := by decide
  rcases family_descends (prefixWord ++ tailWord_4242778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4242811 : List Nat := [1, 1, 1, 1, 1, 6, 1, 1, 2, 8]
def baseStart_4242811 : Nat := 118140960795 + 4242811 * 2 ^ 59
def prefixEnd_4242811 : Nat := 4983230072969 + 3 ^ 40 * 4242811 * 2
def baseEnd_4242811 : Nat := 726200456394434905383391

theorem tailTrace_4242811 : CollatzResearch.WordTrace tailWord_4242811 prefixEnd_4242811 726200456394434905383391 := by
  unfold tailWord_4242811
  simp only [CollatzResearch.WordTrace]
  refine ⟨154748030232027836274408287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103165353488018557516272191 154748030232027836274408287)
  ·
    refine ⟨232122045348041754411612431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154748030232027836274408287 232122045348041754411612431)
    ·
      refine ⟨348183068022062631617418647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232122045348041754411612431 348183068022062631617418647)
      ·
        refine ⟨522274602033093947426127971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 348183068022062631617418647 522274602033093947426127971)
        ·
          refine ⟨783411903049640921139191957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 522274602033093947426127971 783411903049640921139191957)
          ·
            refine ⟨36722432955451918178399623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 783411903049640921139191957 36722432955451918178399623)
            ·
              refine ⟨55083649433177877267599435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36722432955451918178399623 55083649433177877267599435)
              ·
                refine ⟨82625474149766815901399153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55083649433177877267599435 82625474149766815901399153)
                ·
                  refine ⟨61969105612325111926049365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82625474149766815901399153 61969105612325111926049365)
                  ·
                    refine ⟨726200456394434905383391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 61969105612325111926049365 726200456394434905383391)
                    ·
                      rfl

theorem cell23_4242811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 8].length) (baseStart_4242811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4242811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4242811 prefixEnd_4242811 := by exact prefixLift 4242811
  have htrace : WordTrace (prefixWord ++ tailWord_4242811) baseStart_4242811 baseEnd_4242811 := by
    simpa [prefixWord, tailWord_4242811, baseEnd_4242811] using wordTrace_append hprefix tailTrace_4242811
  have hstable : (prefixWord ++ tailWord_4242811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4242811).length < 2 ^ (prefixWord ++ tailWord_4242811).sum := by decide
  have hdescent : baseEnd_4242811 < baseStart_4242811 := by decide
  rcases family_descends (prefixWord ++ tailWord_4242811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4242855 : List Nat := [1, 1, 6, 1, 1, 1, 1, 2, 4, 2, 3]
def baseStart_4242855 : Nat := 118140960795 + 4242855 * 2 ^ 59
def prefixEnd_4242855 : Nat := 4983230072969 + 3 ^ 40 * 4242855 * 2
def baseEnd_4242855 : Nat := 2178623962332102543999971

theorem tailTrace_4242855 : CollatzResearch.WordTrace tailWord_4242855 prefixEnd_4242855 2178623962332102543999971 := by
  unfold tailWord_4242855
  simp only [CollatzResearch.WordTrace]
  refine ⟨154749635043868431789010019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103166423362578954526006679 154749635043868431789010019)
  ·
    refine ⟨232124452565802647683515029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154749635043868431789010019 232124452565802647683515029)
    ·
      refine ⟨10880833714021999110164767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 232124452565802647683515029 10880833714021999110164767)
      ·
        refine ⟨16321250571032998665247151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10880833714021999110164767 16321250571032998665247151)
        ·
          refine ⟨24481875856549497997870727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16321250571032998665247151 24481875856549497997870727)
          ·
            refine ⟨36722813784824246996806091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24481875856549497997870727 36722813784824246996806091)
            ·
              refine ⟨55084220677236370495209137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36722813784824246996806091 55084220677236370495209137)
              ·
                refine ⟨41313165507927277871406853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55084220677236370495209137 41313165507927277871406853)
                ·
                  refine ⟨7746218532736364600888785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41313165507927277871406853 7746218532736364600888785)
                  ·
                    refine ⟨5809663899552273450666589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7746218532736364600888785 5809663899552273450666589)
                    ·
                      refine ⟨2178623962332102543999971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5809663899552273450666589 2178623962332102543999971)
                      ·
                        rfl

theorem cell23_4242855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_4242855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4242855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4242855 prefixEnd_4242855 := by exact prefixLift 4242855
  have htrace : WordTrace (prefixWord ++ tailWord_4242855) baseStart_4242855 baseEnd_4242855 := by
    simpa [prefixWord, tailWord_4242855, baseEnd_4242855] using wordTrace_append hprefix tailTrace_4242855
  have hstable : (prefixWord ++ tailWord_4242855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4242855).length < 2 ^ (prefixWord ++ tailWord_4242855).sum := by decide
  have hdescent : baseEnd_4242855 < baseStart_4242855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4242855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4242878 : List Nat := [4, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8]
def baseStart_4242878 : Nat := 118140960795 + 4242878 * 2 ^ 59
def prefixEnd_4242878 : Nat := 4983230072969 + 3 ^ 40 * 4242878 * 2
def baseEnd_4242878 : Nat := 2178635772387155954012365

theorem tailTrace_4242878 : CollatzResearch.WordTrace tailWord_4242878 prefixEnd_4242878 2178635772387155954012365 := by
  unfold tailWord_4242878
  simp only [CollatzResearch.WordTrace]
  refine ⟨19343809240348138339637161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103166982615190071144731525 19343809240348138339637161)
  ·
    refine ⟨14507856930261103754727871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19343809240348138339637161 14507856930261103754727871)
    ·
      refine ⟨21761785395391655632091807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14507856930261103754727871 21761785395391655632091807)
      ·
        refine ⟨32642678093087483448137711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21761785395391655632091807 32642678093087483448137711)
        ·
          refine ⟨48964017139631225172206567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32642678093087483448137711 48964017139631225172206567)
          ·
            refine ⟨73446025709446837758309851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48964017139631225172206567 73446025709446837758309851)
            ·
              refine ⟨110169038564170256637464777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73446025709446837758309851 110169038564170256637464777)
              ·
                refine ⟨82626778923127692478098583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110169038564170256637464777 82626778923127692478098583)
                ·
                  refine ⟨123940168384691538717147875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82626778923127692478098583 123940168384691538717147875)
                  ·
                    refine ⟨185910252577037308075721813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 123940168384691538717147875 185910252577037308075721813)
                    ·
                      refine ⟨2178635772387155954012365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 185910252577037308075721813 2178635772387155954012365)
                      ·
                        rfl

theorem cell23_4242878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_4242878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4242878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4242878 prefixEnd_4242878 := by exact prefixLift 4242878
  have htrace : WordTrace (prefixWord ++ tailWord_4242878) baseStart_4242878 baseEnd_4242878 := by
    simpa [prefixWord, tailWord_4242878, baseEnd_4242878] using wordTrace_append hprefix tailTrace_4242878
  have hstable : (prefixWord ++ tailWord_4242878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4242878).length < 2 ^ (prefixWord ++ tailWord_4242878).sum := by decide
  have hdescent : baseEnd_4242878 < baseStart_4242878 := by decide
  rcases family_descends (prefixWord ++ tailWord_4242878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4242929 : List Nat := [1, 2, 2, 2, 3, 4, 1, 1, 2, 3, 2]
def baseStart_4242929 : Nat := 118140960795 + 4242929 * 2 ^ 59
def prefixEnd_4242929 : Nat := 4983230072969 + 3 ^ 40 * 4242929 * 2
def baseEnd_4242929 : Nat := 2178661959900535254474631

theorem tailTrace_4242929 : CollatzResearch.WordTrace tailWord_4242929 prefixEnd_4242929 2178661959900535254474631 := by
  unfold tailWord_4242929
  simp only [CollatzResearch.WordTrace]
  refine ⟨154752334045600342427203841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103168222697066894951469227 154752334045600342427203841)
  ·
    refine ⟨116064250534200256820402881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154752334045600342427203841 116064250534200256820402881)
    ·
      refine ⟨87048187900650192615302161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116064250534200256820402881 87048187900650192615302161)
      ·
        refine ⟨65286140925487644461476621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87048187900650192615302161 65286140925487644461476621)
        ·
          refine ⟨24482302847057866673053733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65286140925487644461476621 24482302847057866673053733)
          ·
            refine ⟨4590431783823350001197575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24482302847057866673053733 4590431783823350001197575)
            ·
              refine ⟨6885647675735025001796363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4590431783823350001197575 6885647675735025001796363)
              ·
                refine ⟨10328471513602537502694545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6885647675735025001796363 10328471513602537502694545)
                ·
                  refine ⟨7746353635201903127020909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10328471513602537502694545 7746353635201903127020909)
                  ·
                    refine ⟨2904882613200713672632841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7746353635201903127020909 2904882613200713672632841)
                    ·
                      refine ⟨2178661959900535254474631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2904882613200713672632841 2178661959900535254474631)
                      ·
                        rfl

theorem cell23_4242929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 2, 3, 2].length) (baseStart_4242929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4242929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4242929 prefixEnd_4242929 := by exact prefixLift 4242929
  have htrace : WordTrace (prefixWord ++ tailWord_4242929) baseStart_4242929 baseEnd_4242929 := by
    simpa [prefixWord, tailWord_4242929, baseEnd_4242929] using wordTrace_append hprefix tailTrace_4242929
  have hstable : (prefixWord ++ tailWord_4242929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4242929).length < 2 ^ (prefixWord ++ tailWord_4242929).sum := by decide
  have hdescent : baseEnd_4242929 < baseStart_4242929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4242929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4242952 : List Nat := [2, 1, 3, 2, 1, 1, 5, 2, 2, 4]
def baseStart_4242952 : Nat := 118140960795 + 4242952 * 2 ^ 59
def prefixEnd_4242952 : Nat := 4983230072969 + 3 ^ 40 * 4242952 * 2
def baseEnd_4242952 : Nat := 726224589985196221495675

theorem tailTrace_4242952 : CollatzResearch.WordTrace tailWord_4242952 prefixEnd_4242952 726224589985196221495675 := by
  unfold tailWord_4242952
  simp only [CollatzResearch.WordTrace]
  refine ⟨77376586462258508677645555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103168781949678011570194073 77376586462258508677645555)
  ·
    refine ⟨116064879693387763016468333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77376586462258508677645555 116064879693387763016468333)
    ·
      refine ⟨43524329885020411131175625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116064879693387763016468333 43524329885020411131175625)
      ·
        refine ⟨32643247413765308348381719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43524329885020411131175625 32643247413765308348381719)
        ·
          refine ⟨48964871120647962522572579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32643247413765308348381719 48964871120647962522572579)
          ·
            refine ⟨73447306680971943783858869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48964871120647962522572579 73447306680971943783858869)
            ·
              refine ⟨6885685001341119729736769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 73447306680971943783858869 6885685001341119729736769)
              ·
                refine ⟨5164263751005839797302577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6885685001341119729736769 5164263751005839797302577)
                ·
                  refine ⟨3873197813254379847976933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5164263751005839797302577 3873197813254379847976933)
                  ·
                    refine ⟨726224589985196221495675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3873197813254379847976933 726224589985196221495675)
                    ·
                      rfl

theorem cell23_4242952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 2, 2, 4].length) (baseStart_4242952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4242952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4242952 prefixEnd_4242952 := by exact prefixLift 4242952
  have htrace : WordTrace (prefixWord ++ tailWord_4242952) baseStart_4242952 baseEnd_4242952 := by
    simpa [prefixWord, tailWord_4242952, baseEnd_4242952] using wordTrace_append hprefix tailTrace_4242952
  have hstable : (prefixWord ++ tailWord_4242952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4242952).length < 2 ^ (prefixWord ++ tailWord_4242952).sum := by decide
  have hdescent : baseEnd_4242952 < baseStart_4242952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4242952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4242979 : List Nat := [1, 1, 1, 4, 5, 1, 2, 2, 1, 2, 3]
def baseStart_4242979 : Nat := 118140960795 + 4242979 * 2 ^ 59
def prefixEnd_4242979 : Nat := 4983230072969 + 3 ^ 40 * 4242979 * 2
def baseEnd_4242979 : Nat := 2178687633933260058849401

theorem tailTrace_4242979 : CollatzResearch.WordTrace tailWord_4242979 prefixEnd_4242979 2178687633933260058849401 := by
  unfold tailWord_4242979
  simp only [CollatzResearch.WordTrace]
  refine ⟨154754157695419200966523991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103169438463612800644349327 154754157695419200966523991)
  ·
    refine ⟨232131236543128801449785987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154754157695419200966523991 232131236543128801449785987)
    ·
      refine ⟨348196854814693202174678981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232131236543128801449785987 348196854814693202174678981)
      ·
        refine ⟨65286910277754975407752309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 348196854814693202174678981 65286910277754975407752309)
        ·
          refine ⟨6120647838539528944476779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65286910277754975407752309 6120647838539528944476779)
          ·
            refine ⟨9180971757809293416715169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6120647838539528944476779 9180971757809293416715169)
            ·
              refine ⟨6885728818356970062536377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9180971757809293416715169 6885728818356970062536377)
              ·
                refine ⟨5164296613767727546902283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6885728818356970062536377 5164296613767727546902283)
                ·
                  refine ⟨7746444920651591320353425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5164296613767727546902283 7746444920651591320353425)
                  ·
                    refine ⟨5809833690488693490265069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7746444920651591320353425 5809833690488693490265069)
                    ·
                      refine ⟨2178687633933260058849401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5809833690488693490265069 2178687633933260058849401)
                      ·
                        rfl

theorem cell23_4242979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 2, 1, 2, 3].length) (baseStart_4242979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4242979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4242979 prefixEnd_4242979 := by exact prefixLift 4242979
  have htrace : WordTrace (prefixWord ++ tailWord_4242979) baseStart_4242979 baseEnd_4242979 := by
    simpa [prefixWord, tailWord_4242979, baseEnd_4242979] using wordTrace_append hprefix tailTrace_4242979
  have hstable : (prefixWord ++ tailWord_4242979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4242979).length < 2 ^ (prefixWord ++ tailWord_4242979).sum := by decide
  have hdescent : baseEnd_4242979 < baseStart_4242979 := by decide
  rcases family_descends (prefixWord ++ tailWord_4242979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4243009 : List Nat := [1, 2, 5, 1, 1, 1, 2, 4, 2, 1, 3]
def baseStart_4243009 : Nat := 118140960795 + 4243009 * 2 ^ 59
def prefixEnd_4243009 : Nat := 4983230072969 + 3 ^ 40 * 4243009 * 2
def baseEnd_4243009 : Nat := 2178703038352894941474263

theorem tailTrace_4243009 : CollatzResearch.WordTrace tailWord_4243009 prefixEnd_4243009 2178703038352894941474263 := by
  unfold tailWord_4243009
  simp only [CollatzResearch.WordTrace]
  refine ⟨154755251885310516090116081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103170167923540344060077387 154755251885310516090116081)
  ·
    refine ⟨116066438913982887067587061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154755251885310516090116081 116066438913982887067587061)
    ·
      refine ⟨10881228648185895662586287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 116066438913982887067587061 10881228648185895662586287)
      ·
        refine ⟨16321842972278843493879431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10881228648185895662586287 16321842972278843493879431)
        ·
          refine ⟨24482764458418265240819147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16321842972278843493879431 24482764458418265240819147)
          ·
            refine ⟨36724146687627397861228721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24482764458418265240819147 36724146687627397861228721)
            ·
              refine ⟨27543110015720548395921541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36724146687627397861228721 27543110015720548395921541)
              ·
                refine ⟨5164333127947602824235289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27543110015720548395921541 5164333127947602824235289)
                ·
                  refine ⟨3873249845960702118176467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5164333127947602824235289 3873249845960702118176467)
                  ·
                    refine ⟨5809874768941053177264701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3873249845960702118176467 5809874768941053177264701)
                    ·
                      refine ⟨2178703038352894941474263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5809874768941053177264701 2178703038352894941474263)
                      ·
                        rfl

theorem cell23_4243009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_4243009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4243009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4243009 prefixEnd_4243009 := by exact prefixLift 4243009
  have htrace : WordTrace (prefixWord ++ tailWord_4243009) baseStart_4243009 baseEnd_4243009 := by
    simpa [prefixWord, tailWord_4243009, baseEnd_4243009] using wordTrace_append hprefix tailTrace_4243009
  have hstable : (prefixWord ++ tailWord_4243009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4243009).length < 2 ^ (prefixWord ++ tailWord_4243009).sum := by decide
  have hdescent : baseEnd_4243009 < baseStart_4243009 := by decide
  rcases family_descends (prefixWord ++ tailWord_4243009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4243026 : List Nat := [3, 2, 2, 1, 2, 2, 4, 1, 2, 1, 3]
def baseStart_4243026 : Nat := 118140960795 + 4243026 * 2 ^ 59
def prefixEnd_4243026 : Nat := 4983230072969 + 3 ^ 40 * 4243026 * 2
def baseEnd_4243026 : Nat := 2178711767524021374961685

theorem tailTrace_4243026 : CollatzResearch.WordTrace tailWord_4243026 prefixEnd_4243026 2178711767524021374961685 := by
  unfold tailWord_4243026
  simp only [CollatzResearch.WordTrace]
  refine ⟨38688967981562231998371233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103170581284165951995656621 38688967981562231998371233)
  ·
    refine ⟨29016725986171673998778425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38688967981562231998371233 29016725986171673998778425)
    ·
      refine ⟨21762544489628755499083819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29016725986171673998778425 21762544489628755499083819)
      ·
        refine ⟨32643816734443133248625729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21762544489628755499083819 32643816734443133248625729)
        ·
          refine ⟨24482862550832349936469297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32643816734443133248625729 24482862550832349936469297)
          ·
            refine ⟨18362146913124262452351973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24482862550832349936469297 18362146913124262452351973)
            ·
              refine ⟨3442902546210799209815995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18362146913124262452351973 3442902546210799209815995)
              ·
                refine ⟨5164353819316198814723993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3442902546210799209815995 5164353819316198814723993)
                ·
                  refine ⟨3873265364487149111042995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5164353819316198814723993 3873265364487149111042995)
                  ·
                    refine ⟨5809898046730723666564493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3873265364487149111042995 5809898046730723666564493)
                    ·
                      refine ⟨2178711767524021374961685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5809898046730723666564493 2178711767524021374961685)
                      ·
                        rfl

theorem cell23_4243026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 1, 2, 1, 3].length) (baseStart_4243026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4243026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4243026 prefixEnd_4243026 := by exact prefixLift 4243026
  have htrace : WordTrace (prefixWord ++ tailWord_4243026) baseStart_4243026 baseEnd_4243026 := by
    simpa [prefixWord, tailWord_4243026, baseEnd_4243026] using wordTrace_append hprefix tailTrace_4243026
  have hstable : (prefixWord ++ tailWord_4243026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4243026).length < 2 ^ (prefixWord ++ tailWord_4243026).sum := by decide
  have hdescent : baseEnd_4243026 < baseStart_4243026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4243026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4243030 : List Nat := [5, 2, 2, 2, 1, 2, 1, 2, 1, 2, 3]
def baseStart_4243030 : Nat := 118140960795 + 4243030 * 2 ^ 59
def prefixEnd_4243030 : Nat := 4983230072969 + 3 ^ 40 * 4243030 * 2
def baseEnd_4243030 : Nat := 2178713821446639359311667

theorem tailTrace_4243030 : CollatzResearch.WordTrace tailWord_4243030 prefixEnd_4243030 2178713821446639359311667 := by
  unfold tailWord_4243030
  simp only [CollatzResearch.WordTrace]
  refine ⟨9672251113639652292289409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 103170678545489624451087029 9672251113639652292289409)
  ·
    refine ⟨7254188335229739219217057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9672251113639652292289409 7254188335229739219217057)
    ·
      refine ⟨5440641251422304414412793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7254188335229739219217057 5440641251422304414412793)
      ·
        refine ⟨4080480938566728310809595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5440641251422304414412793 4080480938566728310809595)
        ·
          refine ⟨6120721407850092466214393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4080480938566728310809595 6120721407850092466214393)
          ·
            refine ⟨4590541055887569349660795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6120721407850092466214393 4590541055887569349660795)
            ·
              refine ⟨6885811583831354024491193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4590541055887569349660795 6885811583831354024491193)
              ·
                refine ⟨5164358687873515518368395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6885811583831354024491193 5164358687873515518368395)
                ·
                  refine ⟨7746538031810273277552593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5164358687873515518368395 7746538031810273277552593)
                  ·
                    refine ⟨5809903523857704958164445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7746538031810273277552593 5809903523857704958164445)
                    ·
                      refine ⟨2178713821446639359311667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5809903523857704958164445 2178713821446639359311667)
                      ·
                        rfl

theorem cell23_4243030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_4243030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4243030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4243030 prefixEnd_4243030 := by exact prefixLift 4243030
  have htrace : WordTrace (prefixWord ++ tailWord_4243030) baseStart_4243030 baseEnd_4243030 := by
    simpa [prefixWord, tailWord_4243030, baseEnd_4243030] using wordTrace_append hprefix tailTrace_4243030
  have hstable : (prefixWord ++ tailWord_4243030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4243030).length < 2 ^ (prefixWord ++ tailWord_4243030).sum := by decide
  have hdescent : baseEnd_4243030 < baseStart_4243030 := by decide
  rcases family_descends (prefixWord ++ tailWord_4243030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4243032 : List Nat := [2, 1, 2, 2, 1, 2, 1, 5, 1, 4, 2]
def baseStart_4243032 : Nat := 118140960795 + 4243032 * 2 ^ 59
def prefixEnd_4243032 : Nat := 4983230072969 + 3 ^ 40 * 4243032 * 2
def baseEnd_4243032 : Nat := 2178714848407948351486657

theorem tailTrace_4243032 : CollatzResearch.WordTrace tailWord_4243032 prefixEnd_4243032 2178714848407948351486657 := by
  unfold tailWord_4243032
  simp only [CollatzResearch.WordTrace]
  refine ⟨77378045382113595509101675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103170727176151460678802233 77378045382113595509101675)
  ·
    refine ⟨116067068073170393263652513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77378045382113595509101675 116067068073170393263652513)
    ·
      refine ⟨87050301054877794947739385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116067068073170393263652513 87050301054877794947739385)
      ·
        refine ⟨65287725791158346210804539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87050301054877794947739385 65287725791158346210804539)
        ·
          refine ⟨97931588686737519316206809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65287725791158346210804539 97931588686737519316206809)
          ·
            refine ⟨73448691515053139487155107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97931588686737519316206809 73448691515053139487155107)
            ·
              refine ⟨110173037272579709230732661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73448691515053139487155107 110173037272579709230732661)
              ·
                refine ⟨10328722244304347740381187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 110173037272579709230732661 10328722244304347740381187)
                ·
                  refine ⟨15493083366456521610571781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10328722244304347740381187 15493083366456521610571781)
                  ·
                    refine ⟨2904953131210597801982209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15493083366456521610571781 2904953131210597801982209)
                    ·
                      refine ⟨2178714848407948351486657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2904953131210597801982209 2178714848407948351486657)
                      ·
                        rfl

theorem cell23_4243032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 1, 4, 2].length) (baseStart_4243032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4243032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4243032 prefixEnd_4243032 := by exact prefixLift 4243032
  have htrace : WordTrace (prefixWord ++ tailWord_4243032) baseStart_4243032 baseEnd_4243032 := by
    simpa [prefixWord, tailWord_4243032, baseEnd_4243032] using wordTrace_append hprefix tailTrace_4243032
  have hstable : (prefixWord ++ tailWord_4243032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4243032).length < 2 ^ (prefixWord ++ tailWord_4243032).sum := by decide
  have hdescent : baseEnd_4243032 < baseStart_4243032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4243032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4243036 : List Nat := [2, 2, 4, 1, 2, 1, 3, 2, 1, 3, 2]
def baseStart_4243036 : Nat := 118140960795 + 4243036 * 2 ^ 59
def prefixEnd_4243036 : Nat := 4983230072969 + 3 ^ 40 * 4243036 * 2
def baseEnd_4243036 : Nat := 2178716902330566335836639

theorem tailTrace_4243036 : CollatzResearch.WordTrace tailWord_4243036 prefixEnd_4243036 2178716902330566335836639 := by
  unfold tailWord_4243036
  simp only [CollatzResearch.WordTrace]
  refine ⟨77378118328106349850674481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103170824437475133134232641 77378118328106349850674481)
  ·
    refine ⟨58033588746079762388005861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77378118328106349850674481 58033588746079762388005861)
    ·
      refine ⟨10881297889889955447751099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58033588746079762388005861 10881297889889955447751099)
      ·
        refine ⟨16321946834834933171626649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10881297889889955447751099 16321946834834933171626649)
        ·
          refine ⟨12241460126126199878719987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16321946834834933171626649 12241460126126199878719987)
          ·
            refine ⟨18362190189189299818079981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12241460126126199878719987 18362190189189299818079981)
            ·
              refine ⟨6885821320945987431779993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18362190189189299818079981 6885821320945987431779993)
              ·
                refine ⟨5164365990709490573834995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6885821320945987431779993 5164365990709490573834995)
                ·
                  refine ⟨7746548986064235860752493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5164365990709490573834995 7746548986064235860752493)
                  ·
                    refine ⟨2904955869774088447782185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7746548986064235860752493 2904955869774088447782185)
                    ·
                      refine ⟨2178716902330566335836639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2904955869774088447782185 2178716902330566335836639)
                      ·
                        rfl

theorem cell23_4243036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_4243036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4243036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4243036 prefixEnd_4243036 := by exact prefixLift 4243036
  have htrace : WordTrace (prefixWord ++ tailWord_4243036) baseStart_4243036 baseEnd_4243036 := by
    simpa [prefixWord, tailWord_4243036, baseEnd_4243036] using wordTrace_append hprefix tailTrace_4243036
  have hstable : (prefixWord ++ tailWord_4243036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4243036).length < 2 ^ (prefixWord ++ tailWord_4243036).sum := by decide
  have hdescent : baseEnd_4243036 < baseStart_4243036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4243036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4243053 : List Nat := [1, 5, 1, 1, 4, 1, 3, 1, 1, 3, 2]
def baseStart_4243053 : Nat := 118140960795 + 4243053 * 2 ^ 59
def prefixEnd_4243053 : Nat := 4983230072969 + 3 ^ 40 * 4243053 * 2
def baseEnd_4243053 : Nat := 2178725631501692769324061

theorem tailTrace_4243053 : CollatzResearch.WordTrace tailWord_4243053 prefixEnd_4243053 2178725631501692769324061 := by
  unfold tailWord_4243053
  simp only [CollatzResearch.WordTrace]
  refine ⟨154756856697151111604717813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103171237798100741069811875 154756856697151111604717813)
  ·
    refine ⟨14508455315357916712942295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 154756856697151111604717813 14508455315357916712942295)
    ·
      refine ⟨21762682973036875069413443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14508455315357916712942295 21762682973036875069413443)
      ·
        refine ⟨32644024459555312604120165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21762682973036875069413443 32644024459555312604120165)
        ·
          refine ⟨6120754586166621113272531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32644024459555312604120165 6120754586166621113272531)
          ·
            refine ⟨9181131879249931669908797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6120754586166621113272531 9181131879249931669908797)
            ·
              refine ⟨3442924454718724376215799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9181131879249931669908797 3442924454718724376215799)
              ·
                refine ⟨5164386682078086564323699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3442924454718724376215799 5164386682078086564323699)
                ·
                  refine ⟨7746580023117129846485549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5164386682078086564323699 7746580023117129846485549)
                  ·
                    refine ⟨2904967508668923692432081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7746580023117129846485549 2904967508668923692432081)
                    ·
                      refine ⟨2178725631501692769324061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2904967508668923692432081 2178725631501692769324061)
                      ·
                        rfl

theorem cell23_4243053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 1, 1, 3, 2].length) (baseStart_4243053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4243053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4243053 prefixEnd_4243053 := by exact prefixLift 4243053
  have htrace : WordTrace (prefixWord ++ tailWord_4243053) baseStart_4243053 baseEnd_4243053 := by
    simpa [prefixWord, tailWord_4243053, baseEnd_4243053] using wordTrace_append hprefix tailTrace_4243053
  have hstable : (prefixWord ++ tailWord_4243053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4243053).length < 2 ^ (prefixWord ++ tailWord_4243053).sum := by decide
  have hdescent : baseEnd_4243053 < baseStart_4243053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4243053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4243072 : List Nat := [2, 1, 1, 2, 1, 4, 3, 4, 5]
def baseStart_4243072 : Nat := 118140960795 + 4243072 * 2 ^ 59
def prefixEnd_4243072 : Nat := 4983230072969 + 3 ^ 40 * 4243072 * 2
def baseEnd_4243072 : Nat := 242081709737125354998497

theorem tailTrace_4243072 : CollatzResearch.WordTrace tailWord_4243072 prefixEnd_4243072 242081709737125354998497 := by
  unfold tailWord_4243072
  simp only [CollatzResearch.WordTrace]
  refine ⟨77378774842041138924829735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103171699789388185233106313 77378774842041138924829735)
  ·
    refine ⟨116068162263061708387244603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77378774842041138924829735 116068162263061708387244603)
    ·
      refine ⟨174102243394592562580866905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116068162263061708387244603 174102243394592562580866905)
      ·
        refine ⟨130576682545944421935650179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174102243394592562580866905 130576682545944421935650179)
        ·
          refine ⟨195865023818916632903475269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130576682545944421935650179 195865023818916632903475269)
          ·
            refine ⟨36724691966046868669401613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 195865023818916632903475269 36724691966046868669401613)
            ·
              refine ⟨13771759487267575751025605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36724691966046868669401613 13771759487267575751025605)
              ·
                refine ⟨2582204903862670453317301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13771759487267575751025605 2582204903862670453317301)
                ·
                  refine ⟨242081709737125354998497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2582204903862670453317301 242081709737125354998497)
                  ·
                    rfl

theorem cell23_4243072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 4, 5].length) (baseStart_4243072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4243072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4243072 prefixEnd_4243072 := by exact prefixLift 4243072
  have htrace : WordTrace (prefixWord ++ tailWord_4243072) baseStart_4243072 baseEnd_4243072 := by
    simpa [prefixWord, tailWord_4243072, baseEnd_4243072] using wordTrace_append hprefix tailTrace_4243072
  have hstable : (prefixWord ++ tailWord_4243072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4243072).length < 2 ^ (prefixWord ++ tailWord_4243072).sum := by decide
  have hdescent : baseEnd_4243072 < baseStart_4243072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4243072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4243082 : List Nat := [3, 1, 2, 3, 2, 1, 1, 1, 1, 5, 3]
def baseStart_4243082 : Nat := 118140960795 + 4243082 * 2 ^ 59
def prefixEnd_4243082 : Nat := 4983230072969 + 3 ^ 40 * 4243082 * 2
def baseEnd_4243082 : Nat := 2178740522440673155861427

theorem tailTrace_4243082 : CollatzResearch.WordTrace tailWord_4243082 prefixEnd_4243082 2178740522440673155861427 := by
  unfold tailWord_4243082
  simp only [CollatzResearch.WordTrace]
  refine ⟨38689478603511512389380875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103171942942697366371682333 38689478603511512389380875)
  ·
    refine ⟨58034217905267268584071313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38689478603511512389380875 58034217905267268584071313)
    ·
      refine ⟨43525663428950451438053485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58034217905267268584071313 43525663428950451438053485)
      ·
        refine ⟨16322123785856419289270057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43525663428950451438053485 16322123785856419289270057)
        ·
          refine ⟨12241592839392314466952543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16322123785856419289270057 12241592839392314466952543)
          ·
            refine ⟨18362389259088471700428815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12241592839392314466952543 18362389259088471700428815)
            ·
              refine ⟨27543583888632707550643223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18362389259088471700428815 27543583888632707550643223)
              ·
                refine ⟨41315375832949061325964835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27543583888632707550643223 41315375832949061325964835)
                ·
                  refine ⟨61973063749423591988947253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41315375832949061325964835 61973063749423591988947253)
                  ·
                    refine ⟨5809974726508461748963805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61973063749423591988947253 5809974726508461748963805)
                    ·
                      refine ⟨2178740522440673155861427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5809974726508461748963805 2178740522440673155861427)
                      ·
                        rfl

theorem cell23_4243082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_4243082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4243082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4243082 prefixEnd_4243082 := by exact prefixLift 4243082
  have htrace : WordTrace (prefixWord ++ tailWord_4243082) baseStart_4243082 baseEnd_4243082 := by
    simpa [prefixWord, tailWord_4243082, baseEnd_4243082] using wordTrace_append hprefix tailTrace_4243082
  have hstable : (prefixWord ++ tailWord_4243082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4243082).length < 2 ^ (prefixWord ++ tailWord_4243082).sum := by decide
  have hdescent : baseEnd_4243082 < baseStart_4243082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4243082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4243122 : List Nat := [3, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4]
def baseStart_4243122 : Nat := 118140960795 + 4243122 * 2 ^ 59
def prefixEnd_4243122 : Nat := 4983230072969 + 3 ^ 40 * 4243122 * 2
def baseEnd_4243122 : Nat := 2178761061666852999361243

theorem tailTrace_4243122 : CollatzResearch.WordTrace tailWord_4243122 prefixEnd_4243122 2178761061666852999361243 := by
  unfold tailWord_4243122
  simp only [CollatzResearch.WordTrace]
  refine ⟨38689843333475284097244905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103172915555934090925986413 38689843333475284097244905)
  ·
    refine ⟨29017382500106463072933679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38689843333475284097244905 29017382500106463072933679)
    ·
      refine ⟨43526073750159694609400519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29017382500106463072933679 43526073750159694609400519)
      ·
        refine ⟨65289110625239541914100779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43526073750159694609400519 65289110625239541914100779)
        ·
          refine ⟨97933665937859312871151169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65289110625239541914100779 97933665937859312871151169)
          ·
            refine ⟨73450249453394484653363377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97933665937859312871151169 73450249453394484653363377)
            ·
              refine ⟨55087687090045863490022533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73450249453394484653363377 55087687090045863490022533)
              ·
                refine ⟨10328941329383599404379225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55087687090045863490022533 10328941329383599404379225)
                ·
                  refine ⟨7746705997037699553284419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10328941329383599404379225 7746705997037699553284419)
                  ·
                    refine ⟨11620058995556549329926629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7746705997037699553284419 11620058995556549329926629)
                    ·
                      refine ⟨2178761061666852999361243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11620058995556549329926629 2178761061666852999361243)
                      ·
                        rfl

theorem cell23_4243122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_4243122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4243122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4243122 prefixEnd_4243122 := by exact prefixLift 4243122
  have htrace : WordTrace (prefixWord ++ tailWord_4243122) baseStart_4243122 baseEnd_4243122 := by
    simpa [prefixWord, tailWord_4243122, baseEnd_4243122] using wordTrace_append hprefix tailTrace_4243122
  have hstable : (prefixWord ++ tailWord_4243122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4243122).length < 2 ^ (prefixWord ++ tailWord_4243122).sum := by decide
  have hdescent : baseEnd_4243122 < baseStart_4243122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4243122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4243135 : List Nat := [1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 6]
def baseStart_4243135 : Nat := 118140960795 + 4243135 * 2 ^ 59
def prefixEnd_4243135 : Nat := 4983230072969 + 3 ^ 40 * 4243135 * 2
def baseEnd_4243135 : Nat := 2178767736915361448498683

theorem tailTrace_4243135 : CollatzResearch.WordTrace tailWord_4243135 prefixEnd_4243135 2178767736915361448498683 := by
  unfold tailWord_4243135
  simp only [CollatzResearch.WordTrace]
  refine ⟨154759847482854039609202859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103173231655236026406135239 154759847482854039609202859)
  ·
    refine ⟨232139771224281059413804289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154759847482854039609202859 232139771224281059413804289)
    ·
      refine ⟨174104828418210794560353217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232139771224281059413804289 174104828418210794560353217)
      ·
        refine ⟨130578621313658095920264913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174104828418210794560353217 130578621313658095920264913)
        ·
          refine ⟨97933965985243571940198685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130578621313658095920264913 97933965985243571940198685)
          ·
            refine ⟨36725237244466339477574507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97933965985243571940198685 36725237244466339477574507)
            ·
              refine ⟨55087855866699509216361761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36725237244466339477574507 55087855866699509216361761)
              ·
                refine ⟨41315891900024631912271321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55087855866699509216361761 41315891900024631912271321)
                ·
                  refine ⟨30986918925018473934203491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41315891900024631912271321 30986918925018473934203491)
                  ·
                    refine ⟨46480378387527710901305237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30986918925018473934203491 46480378387527710901305237)
                    ·
                      refine ⟨2178767736915361448498683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46480378387527710901305237 2178767736915361448498683)
                      ·
                        rfl

theorem cell23_4243135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 6].length) (baseStart_4243135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4243135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4243135 prefixEnd_4243135 := by exact prefixLift 4243135
  have htrace : WordTrace (prefixWord ++ tailWord_4243135) baseStart_4243135 baseEnd_4243135 := by
    simpa [prefixWord, tailWord_4243135, baseEnd_4243135] using wordTrace_append hprefix tailTrace_4243135
  have hstable : (prefixWord ++ tailWord_4243135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4243135).length < 2 ^ (prefixWord ++ tailWord_4243135).sum := by decide
  have hdescent : baseEnd_4243135 < baseStart_4243135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4243135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4243226 : List Nat := [3, 1, 1, 3, 2, 3, 3, 1, 1, 5]
def baseStart_4243226 : Nat := 118140960795 + 4243226 * 2 ^ 59
def prefixEnd_4243226 : Nat := 4983230072969 + 3 ^ 40 * 4243226 * 2
def baseEnd_4243226 : Nat := 726271487884973530820255

theorem tailTrace_4243226 : CollatzResearch.WordTrace tailWord_4243226 prefixEnd_4243226 726271487884973530820255 := by
  unfold tailWord_4243226
  simp only [CollatzResearch.WordTrace]
  refine ⟨38690791631381090537691383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103175444350349574767177021 38690791631381090537691383)
  ·
    refine ⟨58036187447071635806537075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38690791631381090537691383 58036187447071635806537075)
    ·
      refine ⟨87054281170607453709805613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58036187447071635806537075 87054281170607453709805613)
      ·
        refine ⟨32645355438977795141177105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87054281170607453709805613 32645355438977795141177105)
        ·
          refine ⟨24484016579233346355882829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32645355438977795141177105 24484016579233346355882829)
          ·
            refine ⟨9181506217212504883456061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24484016579233346355882829 9181506217212504883456061)
            ·
              refine ⟨3443064831454689331296023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9181506217212504883456061 3443064831454689331296023)
              ·
                refine ⟨5164597247182033996944035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3443064831454689331296023 5164597247182033996944035)
                ·
                  refine ⟨7746895870773050995416053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5164597247182033996944035 7746895870773050995416053)
                  ·
                    refine ⟨726271487884973530820255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7746895870773050995416053 726271487884973530820255)
                    ·
                      rfl

theorem cell23_4243226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 1, 1, 5].length) (baseStart_4243226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4243226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4243226 prefixEnd_4243226 := by exact prefixLift 4243226
  have htrace : WordTrace (prefixWord ++ tailWord_4243226) baseStart_4243226 baseEnd_4243226 := by
    simpa [prefixWord, tailWord_4243226, baseEnd_4243226] using wordTrace_append hprefix tailTrace_4243226
  have hstable : (prefixWord ++ tailWord_4243226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4243226).length < 2 ^ (prefixWord ++ tailWord_4243226).sum := by decide
  have hdescent : baseEnd_4243226 < baseStart_4243226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4243226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4243240 : List Nat := [2, 1, 5, 1, 1, 2, 4, 2, 1, 1, 3]
def baseStart_4243240 : Nat := 118140960795 + 4243240 * 2 ^ 59
def prefixEnd_4243240 : Nat := 4983230072969 + 3 ^ 40 * 4243240 * 2
def baseEnd_4243240 : Nat := 2178821652384083537685701

theorem tailTrace_4243240 : CollatzResearch.WordTrace tailWord_4243240 prefixEnd_4243240 2178821652384083537685701 := by
  unfold tailWord_4243240
  simp only [CollatzResearch.WordTrace]
  refine ⟨77381838573736821270887587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103175784764982428361183449 77381838573736821270887587)
  ·
    refine ⟨116072757860605231906331381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77381838573736821270887587 116072757860605231906331381)
    ·
      refine ⟨10881821049431740491218567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 116072757860605231906331381 10881821049431740491218567)
      ·
        refine ⟨16322731574147610736827851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10881821049431740491218567 16322731574147610736827851)
        ·
          refine ⟨24484097361221416105241777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16322731574147610736827851 24484097361221416105241777)
          ·
            refine ⟨18363073020916062078931333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24484097361221416105241777 18363073020916062078931333)
            ·
              refine ⟨3443076191421761639799625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18363073020916062078931333 3443076191421761639799625)
              ·
                refine ⟨2582307143566321229849719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3443076191421761639799625 2582307143566321229849719)
                ·
                  refine ⟨3873460715349481844774579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2582307143566321229849719 3873460715349481844774579)
                  ·
                    refine ⟨5810191073024222767161869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3873460715349481844774579 5810191073024222767161869)
                    ·
                      refine ⟨2178821652384083537685701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5810191073024222767161869 2178821652384083537685701)
                      ·
                        rfl

theorem cell23_4243240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_4243240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4243240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4243240 prefixEnd_4243240 := by exact prefixLift 4243240
  have htrace : WordTrace (prefixWord ++ tailWord_4243240) baseStart_4243240 baseEnd_4243240 := by
    simpa [prefixWord, tailWord_4243240, baseEnd_4243240] using wordTrace_append hprefix tailTrace_4243240
  have hstable : (prefixWord ++ tailWord_4243240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4243240).length < 2 ^ (prefixWord ++ tailWord_4243240).sum := by decide
  have hdescent : baseEnd_4243240 < baseStart_4243240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4243240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4243249 : List Nat := [1, 2, 2, 3, 2, 2, 1, 2, 3, 2, 3]
def baseStart_4243249 : Nat := 118140960795 + 4243249 * 2 ^ 59
def prefixEnd_4243249 : Nat := 4983230072969 + 3 ^ 40 * 4243249 * 2
def baseEnd_4243249 : Nat := 2178826273709974002473159

theorem tailTrace_4243249 : CollatzResearch.WordTrace tailWord_4243249 prefixEnd_4243249 2178826273709974002473159 := by
  unfold tailWord_4243249
  simp only [CollatzResearch.WordTrace]
  refine ⟨154764005404441037078852801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103176003602960691385901867 154764005404441037078852801)
  ·
    refine ⟨116073004053330777809139601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154764005404441037078852801 116073004053330777809139601)
    ·
      refine ⟨87054753039998083356854701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116073004053330777809139601 87054753039998083356854701)
      ·
        refine ⟨32645532389999281258820513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87054753039998083356854701 32645532389999281258820513)
        ·
          refine ⟨24484149292499460944115385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32645532389999281258820513 24484149292499460944115385)
          ·
            refine ⟨18363111969374595708086539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24484149292499460944115385 18363111969374595708086539)
            ·
              refine ⟨27544667954061893562129809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18363111969374595708086539 27544667954061893562129809)
              ·
                refine ⟨20658500965546420171597357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27544667954061893562129809 20658500965546420171597357)
                ·
                  refine ⟨7746937862079907564349009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20658500965546420171597357 7746937862079907564349009)
                  ·
                    refine ⟨5810203396559930673261757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7746937862079907564349009 5810203396559930673261757)
                    ·
                      refine ⟨2178826273709974002473159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5810203396559930673261757 2178826273709974002473159)
                      ·
                        rfl

theorem cell23_4243249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_4243249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4243249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4243249 prefixEnd_4243249 := by exact prefixLift 4243249
  have htrace : WordTrace (prefixWord ++ tailWord_4243249) baseStart_4243249 baseEnd_4243249 := by
    simpa [prefixWord, tailWord_4243249, baseEnd_4243249] using wordTrace_append hprefix tailTrace_4243249
  have hstable : (prefixWord ++ tailWord_4243249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4243249).length < 2 ^ (prefixWord ++ tailWord_4243249).sum := by decide
  have hdescent : baseEnd_4243249 < baseStart_4243249 := by decide
  rcases family_descends (prefixWord ++ tailWord_4243249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4243263 : List Nat := [1, 1, 2, 2, 6, 1, 1, 2, 3, 2, 2]
def baseStart_4243263 : Nat := 118140960795 + 4243263 * 2 ^ 59
def prefixEnd_4243263 : Nat := 4983230072969 + 3 ^ 40 * 4243263 * 2
def baseEnd_4243263 : Nat := 2178833462439136947698095

theorem tailTrace_4243263 : CollatzResearch.WordTrace tailWord_4243263 prefixEnd_4243263 2178833462439136947698095 := by
  unfold tailWord_4243263
  simp only [CollatzResearch.WordTrace]
  refine ⟨154764516026390317469862443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103176344017593544979908295 154764516026390317469862443)
  ·
    refine ⟨232146774039585476204793665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154764516026390317469862443 232146774039585476204793665)
    ·
      refine ⟨174110080529689107153595249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232146774039585476204793665 174110080529689107153595249)
      ·
        refine ⟨130582560397266830365196437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174110080529689107153595249 130582560397266830365196437)
        ·
          refine ⟨6121057518621882673368583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 130582560397266830365196437 6121057518621882673368583)
          ·
            refine ⟨9181586277932824010052875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6121057518621882673368583 9181586277932824010052875)
            ·
              refine ⟨13772379416899236015079313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9181586277932824010052875 13772379416899236015079313)
              ·
                refine ⟨10329284562674427011309485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13772379416899236015079313 10329284562674427011309485)
                ·
                  refine ⟨3873481711002910129241057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10329284562674427011309485 3873481711002910129241057)
                  ·
                    refine ⟨2905111283252182596930793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3873481711002910129241057 2905111283252182596930793)
                    ·
                      refine ⟨2178833462439136947698095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2905111283252182596930793 2178833462439136947698095)
                      ·
                        rfl

theorem cell23_4243263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 3, 2, 2].length) (baseStart_4243263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4243263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4243263 prefixEnd_4243263 := by exact prefixLift 4243263
  have htrace : WordTrace (prefixWord ++ tailWord_4243263) baseStart_4243263 baseEnd_4243263 := by
    simpa [prefixWord, tailWord_4243263, baseEnd_4243263] using wordTrace_append hprefix tailTrace_4243263
  have hstable : (prefixWord ++ tailWord_4243263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4243263).length < 2 ^ (prefixWord ++ tailWord_4243263).sum := by decide
  have hdescent : baseEnd_4243263 < baseStart_4243263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4243263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4243296 : List Nat := [2, 1, 1, 3, 3, 3, 1, 1, 4, 1, 3]
def baseStart_4243296 : Nat := 118140960795 + 4243296 * 2 ^ 59
def prefixEnd_4243296 : Nat := 4983230072969 + 3 ^ 40 * 4243296 * 2
def baseEnd_4243296 : Nat := 2178850407300735318585443

theorem tailTrace_4243296 : CollatzResearch.WordTrace tailWord_4243296 prefixEnd_4243296 2178850407300735318585443 := by
  unfold tailWord_4243296
  simp only [CollatzResearch.WordTrace]
  refine ⟨77382859817635382052906871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103177146423513842737209161 77382859817635382052906871)
  ·
    refine ⟨116074289726453073079360307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77382859817635382052906871 116074289726453073079360307)
    ·
      refine ⟨174111434589679609619040461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116074289726453073079360307 174111434589679609619040461)
      ·
        refine ⟨65291787971129853607140173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 174111434589679609619040461 65291787971129853607140173)
        ·
          refine ⟨24484420489173695102677565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65291787971129853607140173 24484420489173695102677565)
          ·
            refine ⟨9181657683440135663504087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24484420489173695102677565 9181657683440135663504087)
            ·
              refine ⟨13772486525160203495256131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9181657683440135663504087 13772486525160203495256131)
              ·
                refine ⟨20658729787740305242884197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13772486525160203495256131 20658729787740305242884197)
                ·
                  refine ⟨3873511835201307233040787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20658729787740305242884197 3873511835201307233040787)
                  ·
                    refine ⟨5810267752801960849561181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3873511835201307233040787 5810267752801960849561181)
                    ·
                      refine ⟨2178850407300735318585443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5810267752801960849561181 2178850407300735318585443)
                      ·
                        rfl

theorem cell23_4243296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 4, 1, 3].length) (baseStart_4243296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4243296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4243296 prefixEnd_4243296 := by exact prefixLift 4243296
  have htrace : WordTrace (prefixWord ++ tailWord_4243296) baseStart_4243296 baseEnd_4243296 := by
    simpa [prefixWord, tailWord_4243296, baseEnd_4243296] using wordTrace_append hprefix tailTrace_4243296
  have hstable : (prefixWord ++ tailWord_4243296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4243296).length < 2 ^ (prefixWord ++ tailWord_4243296).sum := by decide
  have hdescent : baseEnd_4243296 < baseStart_4243296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4243296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4243313 : List Nat := [1, 2, 2, 2, 1, 3, 5, 1, 2, 1, 3]
def baseStart_4243313 : Nat := 118140960795 + 4243313 * 2 ^ 59
def prefixEnd_4243313 : Nat := 4983230072969 + 3 ^ 40 * 4243313 * 2
def baseEnd_4243313 : Nat := 2178859136471861752072865

theorem tailTrace_4243313 : CollatzResearch.WordTrace tailWord_4243313 prefixEnd_4243313 2178859136471861752072865 := by
  unfold tailWord_4243313
  simp only [CollatzResearch.WordTrace]
  refine ⟨154766339676209176009182593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103177559784139450672788395 154766339676209176009182593)
  ·
    refine ⟨116074754757156882006886945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154766339676209176009182593 116074754757156882006886945)
    ·
      refine ⟨87056066067867661505165209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116074754757156882006886945 87056066067867661505165209)
      ·
        refine ⟨65292049550900746128873907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87056066067867661505165209 65292049550900746128873907)
        ·
          refine ⟨97938074326351119193310861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65292049550900746128873907 97938074326351119193310861)
          ·
            refine ⟨36726777872381669697491573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97938074326351119193310861 36726777872381669697491573)
            ·
              refine ⟨3443135425535781534139835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36726777872381669697491573 3443135425535781534139835)
              ·
                refine ⟨5164703138303672301209753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3443135425535781534139835 5164703138303672301209753)
                ·
                  refine ⟨3873527353727754225907315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5164703138303672301209753 3873527353727754225907315)
                  ·
                    refine ⟨5810291030591631338860973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3873527353727754225907315 5810291030591631338860973)
                    ·
                      refine ⟨2178859136471861752072865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5810291030591631338860973 2178859136471861752072865)
                      ·
                        rfl

theorem cell23_4243313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 1, 2, 1, 3].length) (baseStart_4243313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4243313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4243313 prefixEnd_4243313 := by exact prefixLift 4243313
  have htrace : WordTrace (prefixWord ++ tailWord_4243313) baseStart_4243313 baseEnd_4243313 := by
    simpa [prefixWord, tailWord_4243313, baseEnd_4243313] using wordTrace_append hprefix tailTrace_4243313
  have hstable : (prefixWord ++ tailWord_4243313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4243313).length < 2 ^ (prefixWord ++ tailWord_4243313).sum := by decide
  have hdescent : baseEnd_4243313 < baseStart_4243313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4243313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4243326 : List Nat := [4, 2, 3, 1, 1, 1, 1, 1, 2, 2, 5]
def baseStart_4243326 : Nat := 118140960795 + 4243326 * 2 ^ 59
def prefixEnd_4243326 : Nat := 4983230072969 + 3 ^ 40 * 4243326 * 2
def baseEnd_4243326 : Nat := 2178865811720370201210305

theorem tailTrace_4243326 : CollatzResearch.WordTrace tailWord_4243326 prefixEnd_4243326 2178865811720370201210305 := by
  unfold tailWord_4243326
  simp only [CollatzResearch.WordTrace]
  refine ⟨19345851728145259903675729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103177875883441386152937221 19345851728145259903675729)
  ·
    refine ⟨14509388796108944927756797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19345851728145259903675729 14509388796108944927756797)
    ·
      refine ⟨5441020798540854347908799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14509388796108944927756797 5441020798540854347908799)
      ·
        refine ⟨8161531197811281521863199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5441020798540854347908799 8161531197811281521863199)
        ·
          refine ⟨12242296796716922282794799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8161531197811281521863199 12242296796716922282794799)
          ·
            refine ⟨18363445195075383424192199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12242296796716922282794799 18363445195075383424192199)
            ·
              refine ⟨27545167792613075136288299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18363445195075383424192199 27545167792613075136288299)
              ·
                refine ⟨41317751688919612704432449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27545167792613075136288299 41317751688919612704432449)
                ·
                  refine ⟨30988313766689709528324337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41317751688919612704432449 30988313766689709528324337)
                  ·
                    refine ⟨23241235325017282146243253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30988313766689709528324337 23241235325017282146243253)
                    ·
                      refine ⟨2178865811720370201210305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23241235325017282146243253 2178865811720370201210305)
                      ·
                        rfl

theorem cell23_4243326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_4243326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4243326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4243326 prefixEnd_4243326 := by exact prefixLift 4243326
  have htrace : WordTrace (prefixWord ++ tailWord_4243326) baseStart_4243326 baseEnd_4243326 := by
    simpa [prefixWord, tailWord_4243326, baseEnd_4243326] using wordTrace_append hprefix tailTrace_4243326
  have hstable : (prefixWord ++ tailWord_4243326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4243326).length < 2 ^ (prefixWord ++ tailWord_4243326).sum := by decide
  have hdescent : baseEnd_4243326 < baseStart_4243326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4243326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4243409 : List Nat := [1, 2, 2, 1, 2, 1, 2, 3, 4, 1, 4]
def baseStart_4243409 : Nat := 118140960795 + 4243409 * 2 ^ 59
def prefixEnd_4243409 : Nat := 4983230072969 + 3 ^ 40 * 4243409 * 2
def baseEnd_4243409 : Nat := 2178908430614693376472423

theorem tailTrace_4243409 : CollatzResearch.WordTrace tailWord_4243409 prefixEnd_4243409 2178908430614693376472423 := by
  unfold tailWord_4243409
  simp only [CollatzResearch.WordTrace]
  refine ⟨154769841083861384404677281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103179894055907589603118187 154769841083861384404677281)
  ·
    refine ⟨116077380812896038303507961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154769841083861384404677281 116077380812896038303507961)
    ·
      refine ⟨87058035609672028727630971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116077380812896038303507961 87058035609672028727630971)
      ·
        refine ⟨130587053414508043091446457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87058035609672028727630971 130587053414508043091446457)
        ·
          refine ⟨97940290060881032318584843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130587053414508043091446457 97940290060881032318584843)
          ·
            refine ⟨146910435091321548477877265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97940290060881032318584843 146910435091321548477877265)
            ·
              refine ⟨110182826318491161358407949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146910435091321548477877265 110182826318491161358407949)
              ·
                refine ⟨41318559869434185509402981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110182826318491161358407949 41318559869434185509402981)
                ·
                  refine ⟨7747229975518909783013059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41318559869434185509402981 7747229975518909783013059)
                  ·
                    refine ⟨11620844963278364674519589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7747229975518909783013059 11620844963278364674519589)
                    ·
                      refine ⟨2178908430614693376472423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11620844963278364674519589 2178908430614693376472423)
                      ·
                        rfl

theorem cell23_4243409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 4, 1, 4].length) (baseStart_4243409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4243409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4243409 prefixEnd_4243409 := by exact prefixLift 4243409
  have htrace : WordTrace (prefixWord ++ tailWord_4243409) baseStart_4243409 baseEnd_4243409 := by
    simpa [prefixWord, tailWord_4243409, baseEnd_4243409] using wordTrace_append hprefix tailTrace_4243409
  have hstable : (prefixWord ++ tailWord_4243409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4243409).length < 2 ^ (prefixWord ++ tailWord_4243409).sum := by decide
  have hdescent : baseEnd_4243409 < baseStart_4243409 := by decide
  rcases family_descends (prefixWord ++ tailWord_4243409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4243453 : List Nat := [1, 4, 1, 1, 1, 2, 3, 5, 1, 4]
def baseStart_4243453 : Nat := 118140960795 + 4243453 * 2 ^ 59
def prefixEnd_4243453 : Nat := 4983230072969 + 3 ^ 40 * 4243453 * 2
def baseEnd_4243453 : Nat := 726310341254497068107407

theorem tailTrace_4243453 : CollatzResearch.WordTrace tailWord_4243453 prefixEnd_4243453 726310341254497068107407 := by
  unfold tailWord_4243453
  simp only [CollatzResearch.WordTrace]
  refine ⟨154771445895701979919279013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103180963930467986612852675 154771445895701979919279013)
  ·
    refine ⟨29019646105444121234864815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 154771445895701979919279013 29019646105444121234864815)
    ·
      refine ⟨43529469158166181852297223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29019646105444121234864815 43529469158166181852297223)
      ·
        refine ⟨65294203737249272778445835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43529469158166181852297223 65294203737249272778445835)
        ·
          refine ⟨97941305605873909167668753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65294203737249272778445835 97941305605873909167668753)
          ·
            refine ⟨73455979204405431875751565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97941305605873909167668753 73455979204405431875751565)
            ·
              refine ⟨27545992201652036953406837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73455979204405431875751565 27545992201652036953406837)
              ·
                refine ⟨2582436768904878464381891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27545992201652036953406837 2582436768904878464381891)
                ·
                  refine ⟨3873655153357317696572837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2582436768904878464381891 3873655153357317696572837)
                  ·
                    refine ⟨726310341254497068107407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3873655153357317696572837 726310341254497068107407)
                    ·
                      rfl

theorem cell23_4243453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 5, 1, 4].length) (baseStart_4243453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4243453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4243453 prefixEnd_4243453 := by exact prefixLift 4243453
  have htrace : WordTrace (prefixWord ++ tailWord_4243453) baseStart_4243453 baseEnd_4243453 := by
    simpa [prefixWord, tailWord_4243453, baseEnd_4243453] using wordTrace_append hprefix tailTrace_4243453
  have hstable : (prefixWord ++ tailWord_4243453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4243453).length < 2 ^ (prefixWord ++ tailWord_4243453).sum := by decide
  have hdescent : baseEnd_4243453 < baseStart_4243453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4243453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4243459 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 1, 7, 3]
def baseStart_4243459 : Nat := 118140960795 + 4243459 * 2 ^ 59
def prefixEnd_4243459 : Nat := 4983230072969 + 3 ^ 40 * 4243459 * 2
def baseEnd_4243459 : Nat := 2178934104647418180847193

theorem tailTrace_4243459 : CollatzResearch.WordTrace tailWord_4243459 prefixEnd_4243459 2178934104647418180847193 := by
  unfold tailWord_4243459
  simp only [CollatzResearch.WordTrace]
  refine ⟨154771664733680242943997431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103181109822453495295998287 154771664733680242943997431)
  ·
    refine ⟨232157497100520364415996147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154771664733680242943997431 232157497100520364415996147)
    ·
      refine ⟨348236245650780546623994221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232157497100520364415996147 348236245650780546623994221)
      ·
        refine ⟨130588592119042704983997833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 348236245650780546623994221 130588592119042704983997833)
        ·
          refine ⟨97941444089282028737998375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130588592119042704983997833 97941444089282028737998375)
          ·
            refine ⟨146912166133923043106997563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97941444089282028737998375 146912166133923043106997563)
            ·
              refine ⟨220368249200884564660496345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146912166133923043106997563 220368249200884564660496345)
              ·
                refine ⟨165276186900663423495372259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 220368249200884564660496345 165276186900663423495372259)
                ·
                  refine ⟨247914280350995135243058389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 165276186900663423495372259 247914280350995135243058389)
                  ·
                    refine ⟨5810490945726448482259181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 247914280350995135243058389 5810490945726448482259181)
                    ·
                      refine ⟨2178934104647418180847193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5810490945726448482259181 2178934104647418180847193)
                      ·
                        rfl

theorem cell23_4243459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 7, 3].length) (baseStart_4243459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4243459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4243459 prefixEnd_4243459 := by exact prefixLift 4243459
  have htrace : WordTrace (prefixWord ++ tailWord_4243459) baseStart_4243459 baseEnd_4243459 := by
    simpa [prefixWord, tailWord_4243459, baseEnd_4243459] using wordTrace_append hprefix tailTrace_4243459
  have hstable : (prefixWord ++ tailWord_4243459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4243459).length < 2 ^ (prefixWord ++ tailWord_4243459).sum := by decide
  have hdescent : baseEnd_4243459 < baseStart_4243459 := by decide
  rcases family_descends (prefixWord ++ tailWord_4243459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4243466 : List Nat := [3, 1, 2, 2, 4, 1, 1, 1, 8]
def baseStart_4243466 : Nat := 118140960795 + 4243466 * 2 ^ 59
def prefixEnd_4243466 : Nat := 4983230072969 + 3 ^ 40 * 4243466 * 2
def baseEnd_4243466 : Nat := 242104188779111072606629

theorem tailTrace_4243466 : CollatzResearch.WordTrace tailWord_4243466 prefixEnd_4243466 242104188779111072606629 := by
  unfold tailWord_4243466
  simp only [CollatzResearch.WordTrace]
  refine ⟨38692980011163720784875563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103181280029769922093001501 38692980011163720784875563)
  ·
    refine ⟨58039470016745581177313345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38692980011163720784875563 58039470016745581177313345)
    ·
      refine ⟨43529602512559185882985009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58039470016745581177313345 43529602512559185882985009)
      ·
        refine ⟨32647201884419389412238757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43529602512559185882985009 32647201884419389412238757)
        ·
          refine ⟨6121350353328635514794767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32647201884419389412238757 6121350353328635514794767)
          ·
            refine ⟨9182025529992953272192151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6121350353328635514794767 9182025529992953272192151)
            ·
              refine ⟨13773038294989429908288227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9182025529992953272192151 13773038294989429908288227)
              ·
                refine ⟨20659557442484144862432341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13773038294989429908288227 20659557442484144862432341)
                ·
                  refine ⟨242104188779111072606629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20659557442484144862432341 242104188779111072606629)
                  ·
                    rfl

theorem cell23_4243466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 8].length) (baseStart_4243466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4243466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4243466 prefixEnd_4243466 := by exact prefixLift 4243466
  have htrace : WordTrace (prefixWord ++ tailWord_4243466) baseStart_4243466 baseEnd_4243466 := by
    simpa [prefixWord, tailWord_4243466, baseEnd_4243466] using wordTrace_append hprefix tailTrace_4243466
  have hstable : (prefixWord ++ tailWord_4243466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4243466).length < 2 ^ (prefixWord ++ tailWord_4243466).sum := by decide
  have hdescent : baseEnd_4243466 < baseStart_4243466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4243466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4243493 : List Nat := [1, 3, 1, 2, 2, 3, 2, 2, 3, 1, 3]
def baseStart_4243493 : Nat := 118140960795 + 4243493 * 2 ^ 59
def prefixEnd_4243493 : Nat := 4983230072969 + 3 ^ 40 * 4243493 * 2
def baseEnd_4243493 : Nat := 2178951562989671047822037

theorem tailTrace_4243493 : CollatzResearch.WordTrace tailWord_4243493 prefixEnd_4243493 2178951562989671047822037 := by
  unfold tailWord_4243493
  simp only [CollatzResearch.WordTrace]
  refine ⟨154772904815557066750735133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103181936543704711167156755 154772904815557066750735133)
  ·
    refine ⟨58039839305833900031525675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154772904815557066750735133 58039839305833900031525675)
    ·
      refine ⟨87059758958750850047288513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58039839305833900031525675 87059758958750850047288513)
      ·
        refine ⟨65294819219063137535466385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87059758958750850047288513 65294819219063137535466385)
        ·
          refine ⟨48971114414297353151599789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65294819219063137535466385 48971114414297353151599789)
          ·
            refine ⟨18364167905361507431849921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48971114414297353151599789 18364167905361507431849921)
            ·
              refine ⟨13773125929021130573887441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18364167905361507431849921 13773125929021130573887441)
              ·
                refine ⟨10329844446765847930415581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13773125929021130573887441 10329844446765847930415581)
                ·
                  refine ⟨3873691667537192973905843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10329844446765847930415581 3873691667537192973905843)
                  ·
                    refine ⟨5810537501305789460858765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3873691667537192973905843 5810537501305789460858765)
                    ·
                      refine ⟨2178951562989671047822037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5810537501305789460858765 2178951562989671047822037)
                      ·
                        rfl

theorem cell23_4243493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 3, 1, 3].length) (baseStart_4243493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4243493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4243493 prefixEnd_4243493 := by exact prefixLift 4243493
  have htrace : WordTrace (prefixWord ++ tailWord_4243493) baseStart_4243493 baseEnd_4243493 := by
    simpa [prefixWord, tailWord_4243493, baseEnd_4243493] using wordTrace_append hprefix tailTrace_4243493
  have hstable : (prefixWord ++ tailWord_4243493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4243493).length < 2 ^ (prefixWord ++ tailWord_4243493).sum := by decide
  have hdescent : baseEnd_4243493 < baseStart_4243493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4243493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4243527 : List Nat := [1, 1, 4, 1, 3, 1, 5, 2, 1, 1, 3]
def baseStart_4243527 : Nat := 118140960795 + 4243527 * 2 ^ 59
def prefixEnd_4243527 : Nat := 4983230072969 + 3 ^ 40 * 4243527 * 2
def baseEnd_4243527 : Nat := 2178969021331923914796881

theorem tailTrace_4243527 : CollatzResearch.WordTrace tailWord_4243527 prefixEnd_4243527 2178969021331923914796881 := by
  unfold tailWord_4243527
  simp only [CollatzResearch.WordTrace]
  refine ⟨154774144897433890557472835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103182763264955927038315223 154774144897433890557472835)
  ·
    refine ⟨232161217346150835836209253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154774144897433890557472835 232161217346150835836209253)
    ·
      refine ⟨43530228252403281719289235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 232161217346150835836209253 43530228252403281719289235)
      ·
        refine ⟨65295342378604922578933853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43530228252403281719289235 65295342378604922578933853)
        ·
          refine ⟨24485753391976845967100195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65295342378604922578933853 24485753391976845967100195)
          ·
            refine ⟨36728630087965268950650293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24485753391976845967100195 36728630087965268950650293)
            ·
              refine ⟨3443309070746743964123465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36728630087965268950650293 3443309070746743964123465)
              ·
                refine ⟨2582481803060057973092599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3443309070746743964123465 2582481803060057973092599)
                ·
                  refine ⟨3873722704590086959638899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2582481803060057973092599 3873722704590086959638899)
                  ·
                    refine ⟨5810584056885130439458349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3873722704590086959638899 5810584056885130439458349)
                    ·
                      refine ⟨2178969021331923914796881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5810584056885130439458349 2178969021331923914796881)
                      ·
                        rfl

theorem cell23_4243527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 2, 1, 1, 3].length) (baseStart_4243527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4243527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4243527 prefixEnd_4243527 := by exact prefixLift 4243527
  have htrace : WordTrace (prefixWord ++ tailWord_4243527) baseStart_4243527 baseEnd_4243527 := by
    simpa [prefixWord, tailWord_4243527, baseEnd_4243527] using wordTrace_append hprefix tailTrace_4243527
  have hstable : (prefixWord ++ tailWord_4243527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4243527).length < 2 ^ (prefixWord ++ tailWord_4243527).sum := by decide
  have hdescent : baseEnd_4243527 < baseStart_4243527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4243527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4243529 : List Nat := [1, 2, 1, 1, 2, 2, 3, 1, 3, 1, 6]
def baseStart_4243529 : Nat := 118140960795 + 4243529 * 2 ^ 59
def prefixEnd_4243529 : Nat := 4983230072969 + 3 ^ 40 * 4243529 * 2
def baseEnd_4243529 : Nat := 2178970048293232906971871

theorem tailTrace_4243529 : CollatzResearch.WordTrace tailWord_4243529 prefixEnd_4243529 2178970048293232906971871 := by
  unfold tailWord_4243529
  simp only [CollatzResearch.WordTrace]
  refine ⟨154774217843426644899045641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103182811895617763266030427 154774217843426644899045641)
  ·
    refine ⟨116080663382569983674284231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154774217843426644899045641 116080663382569983674284231)
    ·
      refine ⟨174120995073854975511426347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116080663382569983674284231 174120995073854975511426347)
      ·
        refine ⟨261181492610782463267139521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174120995073854975511426347 261181492610782463267139521)
        ·
          refine ⟨195886119458086847450354641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 261181492610782463267139521 195886119458086847450354641)
          ·
            refine ⟨146914589593565135587765981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 195886119458086847450354641 146914589593565135587765981)
            ·
              refine ⟨55092971097586925845412243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 146914589593565135587765981 55092971097586925845412243)
              ·
                refine ⟨82639456646380388768118365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55092971097586925845412243 82639456646380388768118365)
                ·
                  refine ⟨30989796242392645788044387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82639456646380388768118365 30989796242392645788044387)
                  ·
                    refine ⟨46484694363588968682066581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30989796242392645788044387 46484694363588968682066581)
                    ·
                      refine ⟨2178970048293232906971871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46484694363588968682066581 2178970048293232906971871)
                      ·
                        rfl

theorem cell23_4243529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 1, 6].length) (baseStart_4243529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4243529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4243529 prefixEnd_4243529 := by exact prefixLift 4243529
  have htrace : WordTrace (prefixWord ++ tailWord_4243529) baseStart_4243529 baseEnd_4243529 := by
    simpa [prefixWord, tailWord_4243529, baseEnd_4243529] using wordTrace_append hprefix tailTrace_4243529
  have hstable : (prefixWord ++ tailWord_4243529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4243529).length < 2 ^ (prefixWord ++ tailWord_4243529).sum := by decide
  have hdescent : baseEnd_4243529 < baseStart_4243529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4243529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4243533 : List Nat := [1, 6, 1, 1, 1, 1, 2, 2, 3, 1, 4]
def baseStart_4243533 : Nat := 118140960795 + 4243533 * 2 ^ 59
def prefixEnd_4243533 : Nat := 4983230072969 + 3 ^ 40 * 4243533 * 2
def baseEnd_4243533 : Nat := 2178972102215850891321853

theorem tailTrace_4243533 : CollatzResearch.WordTrace tailWord_4243533 prefixEnd_4243533 2178972102215850891321853 := by
  unfold tailWord_4243533
  simp only [CollatzResearch.WordTrace]
  refine ⟨154774363735412153582191253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103182909156941435721460835 154774363735412153582191253)
  ·
    refine ⟨7255048300097444699165215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 154774363735412153582191253 7255048300097444699165215)
    ·
      refine ⟨10882572450146167048747823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7255048300097444699165215 10882572450146167048747823)
      ·
        refine ⟨16323858675219250573121735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10882572450146167048747823 16323858675219250573121735)
        ·
          refine ⟨24485788012828875859682603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16323858675219250573121735 24485788012828875859682603)
          ·
            refine ⟨36728682019243313789523905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24485788012828875859682603 36728682019243313789523905)
            ·
              refine ⟨27546511514432485342142929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36728682019243313789523905 27546511514432485342142929)
              ·
                refine ⟨20659883635824364006607197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27546511514432485342142929 20659883635824364006607197)
                ·
                  refine ⟨7747456363434136502477699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20659883635824364006607197 7747456363434136502477699)
                  ·
                    refine ⟨11621184545151204753716549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7747456363434136502477699 11621184545151204753716549)
                    ·
                      refine ⟨2178972102215850891321853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11621184545151204753716549 2178972102215850891321853)
                      ·
                        rfl

theorem cell23_4243533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_4243533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4243533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4243533 prefixEnd_4243533 := by exact prefixLift 4243533
  have htrace : WordTrace (prefixWord ++ tailWord_4243533) baseStart_4243533 baseEnd_4243533 := by
    simpa [prefixWord, tailWord_4243533, baseEnd_4243533] using wordTrace_append hprefix tailTrace_4243533
  have hstable : (prefixWord ++ tailWord_4243533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4243533).length < 2 ^ (prefixWord ++ tailWord_4243533).sum := by decide
  have hdescent : baseEnd_4243533 < baseStart_4243533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4243533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4243546 : List Nat := [3, 1, 1, 2, 1, 1, 4, 3, 1, 2, 4]
def baseStart_4243546 : Nat := 118140960795 + 4243546 * 2 ^ 59
def prefixEnd_4243546 : Nat := 4983230072969 + 3 ^ 40 * 4243546 * 2
def baseEnd_4243546 : Nat := 2178978777464359340459293

theorem tailTrace_4243546 : CollatzResearch.WordTrace tailWord_4243546 prefixEnd_4243546 2178978777464359340459293 := by
  unfold tailWord_4243546
  simp only [CollatzResearch.WordTrace]
  refine ⟨38693709471091264200603623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103183225256243371201609661 38693709471091264200603623)
  ·
    refine ⟨58040564206636896300905435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38693709471091264200603623 58040564206636896300905435)
    ·
      refine ⟨87060846309955344451358153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58040564206636896300905435 87060846309955344451358153)
      ·
        refine ⟨65295634732466508338518615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87060846309955344451358153 65295634732466508338518615)
        ·
          refine ⟨97943452098699762507777923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65295634732466508338518615 97943452098699762507777923)
          ·
            refine ⟨146915178148049643761666885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97943452098699762507777923 146915178148049643761666885)
            ·
              refine ⟨27546595902759308205312541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 146915178148049643761666885 27546595902759308205312541)
              ·
                refine ⟨10329973463534740576992203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27546595902759308205312541 10329973463534740576992203)
                ·
                  refine ⟨15494960195302110865488305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10329973463534740576992203 15494960195302110865488305)
                  ·
                    refine ⟨11621220146476583149116229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15494960195302110865488305 11621220146476583149116229)
                    ·
                      refine ⟨2178978777464359340459293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11621220146476583149116229 2178978777464359340459293)
                      ·
                        rfl

theorem cell23_4243546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_4243546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4243546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4243546 prefixEnd_4243546 := by exact prefixLift 4243546
  have htrace : WordTrace (prefixWord ++ tailWord_4243546) baseStart_4243546 baseEnd_4243546 := by
    simpa [prefixWord, tailWord_4243546, baseEnd_4243546] using wordTrace_append hprefix tailTrace_4243546
  have hstable : (prefixWord ++ tailWord_4243546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4243546).length < 2 ^ (prefixWord ++ tailWord_4243546).sum := by decide
  have hdescent : baseEnd_4243546 < baseStart_4243546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4243546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4243579 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 7]
def baseStart_4243579 : Nat := 118140960795 + 4243579 * 2 ^ 59
def prefixEnd_4243579 : Nat := 4983230072969 + 3 ^ 40 * 4243579 * 2
def baseEnd_4243579 : Nat := 2178995722325957711346641

theorem tailTrace_4243579 : CollatzResearch.WordTrace tailWord_4243579 prefixEnd_4243579 2178995722325957711346641 := by
  unfold tailWord_4243579
  simp only [CollatzResearch.WordTrace]
  refine ⟨154776041493245503438365791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103184027662163668958910527 154776041493245503438365791)
  ·
    refine ⟨232164062239868255157548687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154776041493245503438365791 232164062239868255157548687)
    ·
      refine ⟨348246093359802382736323031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232164062239868255157548687 348246093359802382736323031)
      ·
        refine ⟨522369140039703574104484547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 348246093359802382736323031 522369140039703574104484547)
        ·
          refine ⟨783553710059555361156726821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 522369140039703574104484547 783553710059555361156726821)
          ·
            refine ⟨146916320636166630216886279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 783553710059555361156726821 146916320636166630216886279)
            ·
              refine ⟨220374480954249945325329419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146916320636166630216886279 220374480954249945325329419)
              ·
                refine ⟨330561721431374917987994129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 220374480954249945325329419 330561721431374917987994129)
                ·
                  refine ⟨247921291073531188490995597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 330561721431374917987994129 247921291073531188490995597)
                  ·
                    refine ⟨92970484152574195684123349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 247921291073531188490995597 92970484152574195684123349)
                    ·
                      refine ⟨2178995722325957711346641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 92970484152574195684123349 2178995722325957711346641)
                      ·
                        rfl

theorem cell23_4243579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 7].length) (baseStart_4243579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4243579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4243579 prefixEnd_4243579 := by exact prefixLift 4243579
  have htrace : WordTrace (prefixWord ++ tailWord_4243579) baseStart_4243579 baseEnd_4243579 := by
    simpa [prefixWord, tailWord_4243579, baseEnd_4243579] using wordTrace_append hprefix tailTrace_4243579
  have hstable : (prefixWord ++ tailWord_4243579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4243579).length < 2 ^ (prefixWord ++ tailWord_4243579).sum := by decide
  have hdescent : baseEnd_4243579 < baseStart_4243579 := by decide
  rcases family_descends (prefixWord ++ tailWord_4243579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4243593 : List Nat := [1, 2, 1, 1, 4, 2, 1, 1, 5, 3, 2]
def baseStart_4243593 : Nat := 118140960795 + 4243593 * 2 ^ 59
def prefixEnd_4243593 : Nat := 4983230072969 + 3 ^ 40 * 4243593 * 2
def baseEnd_4243593 : Nat := 2179002911055120656571577

theorem tailTrace_4243593 : CollatzResearch.WordTrace tailWord_4243593 prefixEnd_4243593 2179002911055120656571577 := by
  unfold tailWord_4243593
  simp only [CollatzResearch.WordTrace]
  refine ⟨154776552115194783829375433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103184368076796522552916955 154776552115194783829375433)
  ·
    refine ⟨116082414086396087872031575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154776552115194783829375433 116082414086396087872031575)
    ·
      refine ⟨174123621129594131808047363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116082414086396087872031575 174123621129594131808047363)
      ·
        refine ⟨261185431694391197712071045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174123621129594131808047363 261185431694391197712071045)
        ·
          refine ⟨48972268442698349571013321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 261185431694391197712071045 48972268442698349571013321)
          ·
            refine ⟨36729201332023762178259991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48972268442698349571013321 36729201332023762178259991)
            ·
              refine ⟨55093801998035643267389987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36729201332023762178259991 55093801998035643267389987)
              ·
                refine ⟨82640702997053464901084981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55093801998035643267389987 82640702997053464901084981)
                ·
                  refine ⟨7747565905973762334476717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 82640702997053464901084981 7747565905973762334476717)
                  ·
                    refine ⟨2905337214740160875428769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7747565905973762334476717 2905337214740160875428769)
                    ·
                      refine ⟨2179002911055120656571577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2905337214740160875428769 2179002911055120656571577)
                      ·
                        rfl

theorem cell23_4243593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 5, 3, 2].length) (baseStart_4243593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4243593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4243593 prefixEnd_4243593 := by exact prefixLift 4243593
  have htrace : WordTrace (prefixWord ++ tailWord_4243593) baseStart_4243593 baseEnd_4243593 := by
    simpa [prefixWord, tailWord_4243593, baseEnd_4243593] using wordTrace_append hprefix tailTrace_4243593
  have hstable : (prefixWord ++ tailWord_4243593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4243593).length < 2 ^ (prefixWord ++ tailWord_4243593).sum := by decide
  have hdescent : baseEnd_4243593 < baseStart_4243593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4243593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4243640 : List Nat := [2, 1, 2, 1, 2, 1, 5, 1, 4, 2, 2]
def baseStart_4243640 : Nat := 118140960795 + 4243640 * 2 ^ 59
def prefixEnd_4243640 : Nat := 4983230072969 + 3 ^ 40 * 4243640 * 2
def baseEnd_4243640 : Nat := 2179027044645881972683861

theorem tailTrace_4243640 : CollatzResearch.WordTrace tailWord_4243640 prefixEnd_4243640 2179027044645881972683861 := by
  unfold tailWord_4243640
  simp only [CollatzResearch.WordTrace]
  refine ⟨77389133173012255428168187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103185510897349673904224249 77389133173012255428168187)
  ·
    refine ⟨116083699759518383142252281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77389133173012255428168187 116083699759518383142252281)
    ·
      refine ⟨87062774819638787356689211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116083699759518383142252281 87062774819638787356689211)
      ·
        refine ⟨130594162229458181035033817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87062774819638787356689211 130594162229458181035033817)
        ·
          refine ⟨97945621672093635776275363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130594162229458181035033817 97945621672093635776275363)
          ·
            refine ⟨146918432508140453664413045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97945621672093635776275363 146918432508140453664413045)
            ·
              refine ⟨13773603047638167531038723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 146918432508140453664413045 13773603047638167531038723)
              ·
                refine ⟨20660404571457251296558085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13773603047638167531038723 20660404571457251296558085)
                ·
                  refine ⟨3873825857148234618104641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20660404571457251296558085 3873825857148234618104641)
                  ·
                    refine ⟨2905369392861175963578481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3873825857148234618104641 2905369392861175963578481)
                    ·
                      refine ⟨2179027044645881972683861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2905369392861175963578481 2179027044645881972683861)
                      ·
                        rfl

theorem cell23_4243640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 4, 2, 2].length) (baseStart_4243640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4243640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4243640 prefixEnd_4243640 := by exact prefixLift 4243640
  have htrace : WordTrace (prefixWord ++ tailWord_4243640) baseStart_4243640 baseEnd_4243640 := by
    simpa [prefixWord, tailWord_4243640, baseEnd_4243640] using wordTrace_append hprefix tailTrace_4243640
  have hstable : (prefixWord ++ tailWord_4243640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4243640).length < 2 ^ (prefixWord ++ tailWord_4243640).sum := by decide
  have hdescent : baseEnd_4243640 < baseStart_4243640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4243640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4243713 : List Nat := [1, 2, 4, 1, 1, 2, 1, 2, 4, 1, 4]
def baseStart_4243713 : Nat := 118140960795 + 4243713 * 2 ^ 59
def prefixEnd_4243713 : Nat := 4983230072969 + 3 ^ 40 * 4243713 * 2
def baseEnd_4243713 : Nat := 2179064528733660187071025

theorem tailTrace_4243713 : CollatzResearch.WordTrace tailWord_4243713 prefixEnd_4243713 2179064528733660187071025 := by
  unfold tailWord_4243713
  simp only [CollatzResearch.WordTrace]
  refine ⟨154780928874760044323743793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103187285916506696215829195 154780928874760044323743793)
  ·
    refine ⟨116085696656070033242807845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154780928874760044323743793 116085696656070033242807845)
    ·
      refine ⟨21766068123013131233026471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116085696656070033242807845 21766068123013131233026471)
      ·
        refine ⟨32649102184519696849539707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21766068123013131233026471 32649102184519696849539707)
        ·
          refine ⟨48973653276779545274309561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32649102184519696849539707 48973653276779545274309561)
          ·
            refine ⟨36730239957584658955732171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48973653276779545274309561 36730239957584658955732171)
            ·
              refine ⟨55095359936376988433598257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36730239957584658955732171 55095359936376988433598257)
              ·
                refine ⟨41321519952282741325198693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55095359936376988433598257 41321519952282741325198693)
                ·
                  refine ⟨7747784991053013998474755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41321519952282741325198693 7747784991053013998474755)
                  ·
                    refine ⟨11621677486579520997712133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7747784991053013998474755 11621677486579520997712133)
                    ·
                      refine ⟨2179064528733660187071025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11621677486579520997712133 2179064528733660187071025)
                      ·
                        rfl

theorem cell23_4243713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_4243713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4243713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4243713 prefixEnd_4243713 := by exact prefixLift 4243713
  have htrace : WordTrace (prefixWord ++ tailWord_4243713) baseStart_4243713 baseEnd_4243713 := by
    simpa [prefixWord, tailWord_4243713, baseEnd_4243713] using wordTrace_append hprefix tailTrace_4243713
  have hstable : (prefixWord ++ tailWord_4243713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4243713).length < 2 ^ (prefixWord ++ tailWord_4243713).sum := by decide
  have hdescent : baseEnd_4243713 < baseStart_4243713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4243713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4243723 : List Nat := [1, 1, 1, 1, 5, 2, 2, 1, 5, 4]
def baseStart_4243723 : Nat := 118140960795 + 4243723 * 2 ^ 59
def prefixEnd_4243723 : Nat := 4983230072969 + 3 ^ 40 * 4243723 * 2
def baseEnd_4243723 : Nat := 726356554513401715981993

theorem tailTrace_4243723 : CollatzResearch.WordTrace tailWord_4243723 prefixEnd_4243723 726356554513401715981993 := by
  unfold tailWord_4243723
  simp only [CollatzResearch.WordTrace]
  refine ⟨154781293604723816031607823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103187529069815877354405215 154781293604723816031607823)
  ·
    refine ⟨232171940407085724047411735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154781293604723816031607823 232171940407085724047411735)
    ·
      refine ⟨348257910610628586071117603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232171940407085724047411735 348257910610628586071117603)
      ·
        refine ⟨522386865915942879106676405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 348257910610628586071117603 522386865915942879106676405)
        ·
          refine ⟨48973768679619644916250913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 522386865915942879106676405 48973768679619644916250913)
          ·
            refine ⟨36730326509714733687188185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48973768679619644916250913 36730326509714733687188185)
            ·
              refine ⟨27547744882286050265391139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36730326509714733687188185 27547744882286050265391139)
              ·
                refine ⟨41321617323429075398086709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27547744882286050265391139 41321617323429075398086709)
                ·
                  refine ⟨3873901624071475818570629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41321617323429075398086709 3873901624071475818570629)
                  ·
                    refine ⟨726356554513401715981993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3873901624071475818570629 726356554513401715981993)
                    ·
                      rfl

theorem cell23_4243723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 5, 4].length) (baseStart_4243723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4243723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4243723 prefixEnd_4243723 := by exact prefixLift 4243723
  have htrace : WordTrace (prefixWord ++ tailWord_4243723) baseStart_4243723 baseEnd_4243723 := by
    simpa [prefixWord, tailWord_4243723, baseEnd_4243723] using wordTrace_append hprefix tailTrace_4243723
  have hstable : (prefixWord ++ tailWord_4243723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4243723).length < 2 ^ (prefixWord ++ tailWord_4243723).sum := by decide
  have hdescent : baseEnd_4243723 < baseStart_4243723 := by decide
  rcases family_descends (prefixWord ++ tailWord_4243723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4243733 : List Nat := [1, 3, 2, 1, 2, 1, 2, 3, 1, 4, 3]
def baseStart_4243733 : Nat := 118140960795 + 4243733 * 2 ^ 59
def prefixEnd_4243733 : Nat := 4983230072969 + 3 ^ 40 * 4243733 * 2
def baseEnd_4243733 : Nat := 2179074798346750108820933

theorem tailTrace_4243733 : CollatzResearch.WordTrace tailWord_4243733 prefixEnd_4243733 2179074798346750108820933 := by
  unfold tailWord_4243733
  simp only [CollatzResearch.WordTrace]
  refine ⟨154781658334687587739471853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103187772223125058492981235 154781658334687587739471853)
  ·
    refine ⟨58043121875507845402301945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154781658334687587739471853 58043121875507845402301945)
    ·
      refine ⟨43532341406630884051726459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58043121875507845402301945 43532341406630884051726459)
      ·
        refine ⟨65298512109946326077589689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43532341406630884051726459 65298512109946326077589689)
        ·
          refine ⟨48973884082459744558192267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65298512109946326077589689 48973884082459744558192267)
          ·
            refine ⟨73460826123689616837288401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48973884082459744558192267 73460826123689616837288401)
            ·
              refine ⟨55095619592767212627966301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73460826123689616837288401 55095619592767212627966301)
              ·
                refine ⟨20660857347287704735487363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55095619592767212627966301 20660857347287704735487363)
                ·
                  refine ⟨30991286020931557103231045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20660857347287704735487363 30991286020931557103231045)
                  ·
                    refine ⟨5810866128924666956855821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30991286020931557103231045 5810866128924666956855821)
                    ·
                      refine ⟨2179074798346750108820933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5810866128924666956855821 2179074798346750108820933)
                      ·
                        rfl

theorem cell23_4243733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 4, 3].length) (baseStart_4243733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4243733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4243733 prefixEnd_4243733 := by exact prefixLift 4243733
  have htrace : WordTrace (prefixWord ++ tailWord_4243733) baseStart_4243733 baseEnd_4243733 := by
    simpa [prefixWord, tailWord_4243733, baseEnd_4243733] using wordTrace_append hprefix tailTrace_4243733
  have hstable : (prefixWord ++ tailWord_4243733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4243733).length < 2 ^ (prefixWord ++ tailWord_4243733).sum := by decide
  have hdescent : baseEnd_4243733 < baseStart_4243733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4243733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4243783 : List Nat := [1, 1, 4, 1, 2, 2, 1, 3, 3, 5]
def baseStart_4243783 : Nat := 118140960795 + 4243783 * 2 ^ 59
def prefixEnd_4243783 : Nat := 4983230072969 + 3 ^ 40 * 4243783 * 2
def baseEnd_4243783 : Nat := 726366824126491637731901

theorem tailTrace_4243783 : CollatzResearch.WordTrace tailWord_4243783 prefixEnd_4243783 726366824126491637731901 := by
  unfold tailWord_4243783
  simp only [CollatzResearch.WordTrace]
  refine ⟨154783481984506446278792003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103188987989670964185861335 154783481984506446278792003)
  ·
    refine ⟨232175222976759669418188005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154783481984506446278792003 232175222976759669418188005)
    ·
      refine ⟨43532854308142438015910251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 232175222976759669418188005 43532854308142438015910251)
      ·
        refine ⟨65299281462213657023865377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43532854308142438015910251 65299281462213657023865377)
        ·
          refine ⟨48974461096660242767899033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65299281462213657023865377 48974461096660242767899033)
          ·
            refine ⟨36730845822495182075924275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48974461096660242767899033 36730845822495182075924275)
            ·
              refine ⟨55096268733742773113886413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36730845822495182075924275 55096268733742773113886413)
              ·
                refine ⟨20661100775153539917707405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55096268733742773113886413 20661100775153539917707405)
                ·
                  refine ⟨7747912790682577469140277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20661100775153539917707405 7747912790682577469140277)
                  ·
                    refine ⟨726366824126491637731901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7747912790682577469140277 726366824126491637731901)
                    ·
                      rfl

theorem cell23_4243783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 3, 5].length) (baseStart_4243783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4243783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4243783 prefixEnd_4243783 := by exact prefixLift 4243783
  have htrace : WordTrace (prefixWord ++ tailWord_4243783) baseStart_4243783 baseEnd_4243783 := by
    simpa [prefixWord, tailWord_4243783, baseEnd_4243783] using wordTrace_append hprefix tailTrace_4243783
  have hstable : (prefixWord ++ tailWord_4243783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4243783).length < 2 ^ (prefixWord ++ tailWord_4243783).sum := by decide
  have hdescent : baseEnd_4243783 < baseStart_4243783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4243783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4243804 : List Nat := [2, 2, 4, 3, 1, 2, 1, 2, 6]
def baseStart_4243804 : Nat := 118140960795 + 4243804 * 2 ^ 59
def prefixEnd_4243804 : Nat := 4983230072969 + 3 ^ 40 * 4243804 * 2
def baseEnd_4243804 : Nat := 242123472830357703448123

theorem tailTrace_4243804 : CollatzResearch.WordTrace tailWord_4243804 prefixEnd_4243804 242123472830357703448123 := by
  unfold tailWord_4243804
  simp only [CollatzResearch.WordTrace]
  refine ⟨77392123958715183432653233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103189498611620244576870977 77392123958715183432653233)
  ·
    refine ⟨58044092969036387574489925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77392123958715183432653233 58044092969036387574489925)
    ·
      refine ⟨10883267431694322670216861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58044092969036387574489925 10883267431694322670216861)
      ·
        refine ⟨4081225286885371001331323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10883267431694322670216861 4081225286885371001331323)
        ·
          refine ⟨6121837930328056501996985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4081225286885371001331323 6121837930328056501996985)
          ·
            refine ⟨4591378447746042376497739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6121837930328056501996985 4591378447746042376497739)
            ·
              refine ⟨6887067671619063564746609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4591378447746042376497739 6887067671619063564746609)
              ·
                refine ⟨5165300753714297673559957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6887067671619063564746609 5165300753714297673559957)
                ·
                  refine ⟨242123472830357703448123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5165300753714297673559957 242123472830357703448123)
                  ·
                    rfl

theorem cell23_4243804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 2, 6].length) (baseStart_4243804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4243804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4243804 prefixEnd_4243804 := by exact prefixLift 4243804
  have htrace : WordTrace (prefixWord ++ tailWord_4243804) baseStart_4243804 baseEnd_4243804 := by
    simpa [prefixWord, tailWord_4243804, baseEnd_4243804] using wordTrace_append hprefix tailTrace_4243804
  have hstable : (prefixWord ++ tailWord_4243804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4243804).length < 2 ^ (prefixWord ++ tailWord_4243804).sum := by decide
  have hdescent : baseEnd_4243804 < baseStart_4243804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4243804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4243823 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 2, 6, 3]
def baseStart_4243823 : Nat := 118140960795 + 4243823 * 2 ^ 59
def prefixEnd_4243823 : Nat := 4983230072969 + 3 ^ 40 * 4243823 * 2
def baseEnd_4243823 : Nat := 2179121011605654756695519

theorem tailTrace_4243823 : CollatzResearch.WordTrace tailWord_4243823 prefixEnd_4243823 2179121011605654756695519 := by
  unfold tailWord_4243823
  simp only [CollatzResearch.WordTrace]
  refine ⟨154784940904361533110248123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103189960602907688740165415 154784940904361533110248123)
  ·
    refine ⟨232177411356542299665372185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154784940904361533110248123 232177411356542299665372185)
    ·
      refine ⟨174133058517406724749029139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232177411356542299665372185 174133058517406724749029139)
      ·
        refine ⟨261199587776110087123543709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174133058517406724749029139 261199587776110087123543709)
        ·
          refine ⟨97949845416041282671328891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 261199587776110087123543709 97949845416041282671328891)
          ·
            refine ⟨146924768124061924006993337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97949845416041282671328891 146924768124061924006993337)
            ·
              refine ⟨110193576093046443005245003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146924768124061924006993337 110193576093046443005245003)
              ·
                refine ⟨165290364139569664507867505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110193576093046443005245003 165290364139569664507867505)
                ·
                  refine ⟨123967773104677248380900629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 165290364139569664507867505 123967773104677248380900629)
                  ·
                    refine ⟨5810989364281746017854717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 123967773104677248380900629 5810989364281746017854717)
                    ·
                      refine ⟨2179121011605654756695519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5810989364281746017854717 2179121011605654756695519)
                      ·
                        rfl

theorem cell23_4243823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 6, 3].length) (baseStart_4243823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4243823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4243823 prefixEnd_4243823 := by exact prefixLift 4243823
  have htrace : WordTrace (prefixWord ++ tailWord_4243823) baseStart_4243823 baseEnd_4243823 := by
    simpa [prefixWord, tailWord_4243823, baseEnd_4243823] using wordTrace_append hprefix tailTrace_4243823
  have hstable : (prefixWord ++ tailWord_4243823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4243823).length < 2 ^ (prefixWord ++ tailWord_4243823).sum := by decide
  have hdescent : baseEnd_4243823 < baseStart_4243823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4243823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4243837 : List Nat := [1, 4, 1, 1, 2, 4, 2, 2, 1, 1, 4]
def baseStart_4243837 : Nat := 118140960795 + 4243837 * 2 ^ 59
def prefixEnd_4243837 : Nat := 4983230072969 + 3 ^ 40 * 4243837 * 2
def baseEnd_4243837 : Nat := 2179128200334817701920455

theorem tailTrace_4243837 : CollatzResearch.WordTrace tailWord_4243837 prefixEnd_4243837 2179128200334817701920455 := by
  unfold tailWord_4243837
  simp only [CollatzResearch.WordTrace]
  refine ⟨154785451526310813501257765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103190301017540542334171843 154785451526310813501257765)
  ·
    refine ⟨29022272161183277531485831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 154785451526310813501257765 29022272161183277531485831)
    ·
      refine ⟨43533408241774916297228747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29022272161183277531485831 43533408241774916297228747)
      ·
        refine ⟨65300112362662374445843121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43533408241774916297228747 65300112362662374445843121)
        ·
          refine ⟨48975084271996780834382341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65300112362662374445843121 48975084271996780834382341)
          ·
            refine ⟨9182828300999396406446689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48975084271996780834382341 9182828300999396406446689)
            ·
              refine ⟨6887121225749547304835017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9182828300999396406446689 6887121225749547304835017)
              ·
                refine ⟨5165340919312160478626263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6887121225749547304835017 5165340919312160478626263)
                ·
                  refine ⟨7748011378968240717939395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5165340919312160478626263 7748011378968240717939395)
                  ·
                    refine ⟨11622017068452361076909093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7748011378968240717939395 11622017068452361076909093)
                    ·
                      refine ⟨2179128200334817701920455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11622017068452361076909093 2179128200334817701920455)
                      ·
                        rfl

theorem cell23_4243837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 2, 1, 1, 4].length) (baseStart_4243837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4243837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4243837 prefixEnd_4243837 := by exact prefixLift 4243837
  have htrace : WordTrace (prefixWord ++ tailWord_4243837) baseStart_4243837 baseEnd_4243837 := by
    simpa [prefixWord, tailWord_4243837, baseEnd_4243837] using wordTrace_append hprefix tailTrace_4243837
  have hstable : (prefixWord ++ tailWord_4243837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4243837).length < 2 ^ (prefixWord ++ tailWord_4243837).sum := by decide
  have hdescent : baseEnd_4243837 < baseStart_4243837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4243837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4243903 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 6, 6]
def baseStart_4243903 : Nat := 118140960795 + 4243903 * 2 ^ 59
def prefixEnd_4243903 : Nat := 4983230072969 + 3 ^ 40 * 4243903 * 2
def baseEnd_4243903 : Nat := 726387363352671481231717

theorem tailTrace_4243903 : CollatzResearch.WordTrace tailWord_4243903 prefixEnd_4243903 726387363352671481231717 := by
  unfold tailWord_4243903
  simp only [CollatzResearch.WordTrace]
  refine ⟨154787858744071706773160363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103191905829381137848773575 154787858744071706773160363)
  ·
    refine ⟨232181788116107560159740545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154787858744071706773160363 232181788116107560159740545)
    ·
      refine ⟨174136341087080670119805409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232181788116107560159740545 174136341087080670119805409)
      ·
        refine ⟨130602255815310502589854057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174136341087080670119805409 130602255815310502589854057)
        ·
          refine ⟨97951691861482876942390543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130602255815310502589854057 97951691861482876942390543)
          ·
            refine ⟨146927537792224315413585815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97951691861482876942390543 146927537792224315413585815)
            ·
              refine ⟨220391306688336473120378723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146927537792224315413585815 220391306688336473120378723)
              ·
                refine ⟨330586960032504709680568085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 220391306688336473120378723 330586960032504709680568085)
                ·
                  refine ⟨15496263751523658266276629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 330586960032504709680568085 15496263751523658266276629)
                  ·
                    refine ⟨726387363352671481231717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15496263751523658266276629 726387363352671481231717)
                    ·
                      rfl

theorem cell23_4243903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 6].length) (baseStart_4243903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4243903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4243903 prefixEnd_4243903 := by exact prefixLift 4243903
  have htrace : WordTrace (prefixWord ++ tailWord_4243903) baseStart_4243903 baseEnd_4243903 := by
    simpa [prefixWord, tailWord_4243903, baseEnd_4243903] using wordTrace_append hprefix tailTrace_4243903
  have hstable : (prefixWord ++ tailWord_4243903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4243903).length < 2 ^ (prefixWord ++ tailWord_4243903).sum := by decide
  have hdescent : baseEnd_4243903 < baseStart_4243903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4243903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4243922 : List Nat := [3, 2, 2, 4, 1, 2, 2, 2, 1, 2, 2]
def baseStart_4243922 : Nat := 118140960795 + 4243922 * 2 ^ 59
def prefixEnd_4243922 : Nat := 4983230072969 + 3 ^ 40 * 4243922 * 2
def baseEnd_4243922 : Nat := 2179171846190449869357565

theorem tailTrace_4243922 : CollatzResearch.WordTrace tailWord_4243922 prefixEnd_4243922 2179171846190449869357565 := by
  unfold tailWord_4243922
  simp only [CollatzResearch.WordTrace]
  refine ⟨38697137932750718254525505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103192367820668582012068013 38697137932750718254525505)
  ·
    refine ⟨29022853449563038690894129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38697137932750718254525505 29022853449563038690894129)
    ·
      refine ⟨21767140087172279018170597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29022853449563038690894129 21767140087172279018170597)
      ·
        refine ⟨4081338766344802315906987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21767140087172279018170597 4081338766344802315906987)
        ·
          refine ⟨6122008149517203473860481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4081338766344802315906987 6122008149517203473860481)
          ·
            refine ⟨4591506112137902605395361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6122008149517203473860481 4591506112137902605395361)
            ·
              refine ⟨3443629584103426954046521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4591506112137902605395361 3443629584103426954046521)
              ·
                refine ⟨2582722188077570215534891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3443629584103426954046521 2582722188077570215534891)
                ·
                  refine ⟨3874083282116355323302337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2582722188077570215534891 3874083282116355323302337)
                  ·
                    refine ⟨2905562461587266492476753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3874083282116355323302337 2905562461587266492476753)
                    ·
                      refine ⟨2179171846190449869357565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2905562461587266492476753 2179171846190449869357565)
                      ·
                        rfl

theorem cell23_4243922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_4243922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4243922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4243922 prefixEnd_4243922 := by exact prefixLift 4243922
  have htrace : WordTrace (prefixWord ++ tailWord_4243922) baseStart_4243922 baseEnd_4243922 := by
    simpa [prefixWord, tailWord_4243922, baseEnd_4243922] using wordTrace_append hprefix tailTrace_4243922
  have hstable : (prefixWord ++ tailWord_4243922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4243922).length < 2 ^ (prefixWord ++ tailWord_4243922).sum := by decide
  have hdescent : baseEnd_4243922 < baseStart_4243922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4243922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4243930 : List Nat := [3, 1, 1, 2, 3, 1, 1, 1, 1, 6, 3]
def baseStart_4243930 : Nat := 118140960795 + 4243930 * 2 ^ 59
def prefixEnd_4243930 : Nat := 4983230072969 + 3 ^ 40 * 4243930 * 2
def baseEnd_4243930 : Nat := 2179175954035685838057527

theorem tailTrace_4243930 : CollatzResearch.WordTrace tailWord_4243930 prefixEnd_4243930 2179175954035685838057527 := by
  unfold tailWord_4243930
  simp only [CollatzResearch.WordTrace]
  refine ⟨38697210878743472596098311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103192562343315926922928829 38697210878743472596098311)
  ·
    refine ⟨58045816318115208894147467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38697210878743472596098311 58045816318115208894147467)
    ·
      refine ⟨87068724477172813341221201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58045816318115208894147467 87068724477172813341221201)
      ·
        refine ⟨65301543357879610005915901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87068724477172813341221201 65301543357879610005915901)
        ·
          refine ⟨24488078759204853752218463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65301543357879610005915901 24488078759204853752218463)
          ·
            refine ⟨36732118138807280628327695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24488078759204853752218463 36732118138807280628327695)
            ·
              refine ⟨55098177208210920942491543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36732118138807280628327695 55098177208210920942491543)
              ·
                refine ⟨82647265812316381413737315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55098177208210920942491543 82647265812316381413737315)
                ·
                  refine ⟨123970898718474572120605973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82647265812316381413737315 123970898718474572120605973)
                  ·
                    refine ⟨5811135877428495568153405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 123970898718474572120605973 5811135877428495568153405)
                    ·
                      refine ⟨2179175954035685838057527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5811135877428495568153405 2179175954035685838057527)
                      ·
                        rfl

theorem cell23_4243930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 1, 6, 3].length) (baseStart_4243930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4243930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4243930 prefixEnd_4243930 := by exact prefixLift 4243930
  have htrace : WordTrace (prefixWord ++ tailWord_4243930) baseStart_4243930 baseEnd_4243930 := by
    simpa [prefixWord, tailWord_4243930, baseEnd_4243930] using wordTrace_append hprefix tailTrace_4243930
  have hstable : (prefixWord ++ tailWord_4243930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4243930).length < 2 ^ (prefixWord ++ tailWord_4243930).sum := by decide
  have hdescent : baseEnd_4243930 < baseStart_4243930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4243930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4243944 : List Nat := [2, 1, 4, 1, 1, 4, 2, 1, 1, 4, 2]
def baseStart_4243944 : Nat := 118140960795 + 4243944 * 2 ^ 59
def prefixEnd_4243944 : Nat := 4983230072969 + 3 ^ 40 * 4243944 * 2
def baseEnd_4243944 : Nat := 2179183142764848783282463

theorem tailTrace_4243944 : CollatzResearch.WordTrace tailWord_4243944 prefixEnd_4243944 2179183142764848783282463 := by
  unfold tailWord_4243944
  simp only [CollatzResearch.WordTrace]
  refine ⟨77394677068461585387701443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103192902757948780516935257 77394677068461585387701443)
  ·
    refine ⟨116092015602692378081552165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77394677068461585387701443 116092015602692378081552165)
    ·
      refine ⟨21767252925504820890291031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116092015602692378081552165 21767252925504820890291031)
      ·
        refine ⟨32650879388257231335436547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21767252925504820890291031 32650879388257231335436547)
        ·
          refine ⟨48976319082385847003154821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32650879388257231335436547 48976319082385847003154821)
          ·
            refine ⟨9183059827947346313091529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48976319082385847003154821 9183059827947346313091529)
            ·
              refine ⟨6887294870960509734818647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9183059827947346313091529 6887294870960509734818647)
              ·
                refine ⟨10330942306440764602227971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6887294870960509734818647 10330942306440764602227971)
                ·
                  refine ⟨15496413459661146903341957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10330942306440764602227971 15496413459661146903341957)
                  ·
                    refine ⟨2905577523686465044376617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15496413459661146903341957 2905577523686465044376617)
                    ·
                      refine ⟨2179183142764848783282463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2905577523686465044376617 2179183142764848783282463)
                      ·
                        rfl

theorem cell23_4243944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 1, 4, 2].length) (baseStart_4243944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4243944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4243944 prefixEnd_4243944 := by exact prefixLift 4243944
  have htrace : WordTrace (prefixWord ++ tailWord_4243944) baseStart_4243944 baseEnd_4243944 := by
    simpa [prefixWord, tailWord_4243944, baseEnd_4243944] using wordTrace_append hprefix tailTrace_4243944
  have hstable : (prefixWord ++ tailWord_4243944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4243944).length < 2 ^ (prefixWord ++ tailWord_4243944).sum := by decide
  have hdescent : baseEnd_4243944 < baseStart_4243944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4243944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4243950 : List Nat := [4, 1, 2, 1, 2, 2, 1, 1, 9]
def baseStart_4243950 : Nat := 118140960795 + 4243950 * 2 ^ 59
def prefixEnd_4243950 : Nat := 4983230072969 + 3 ^ 40 * 4243950 * 2
def baseEnd_4243950 : Nat := 242131802627641751089715

theorem tailTrace_4243950 : CollatzResearch.WordTrace tailWord_4243950 prefixEnd_4243950 242131802627641751089715 := by
  unfold tailWord_4243950
  simp only [CollatzResearch.WordTrace]
  refine ⟨19348696621862679225015163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103193048649934289200080869 19348696621862679225015163)
  ·
    refine ⟨29023044932794018837522745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19348696621862679225015163 29023044932794018837522745)
    ·
      refine ⟨21767283699595514128142059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29023044932794018837522745 21767283699595514128142059)
      ·
        refine ⟨32650925549393271192213089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21767283699595514128142059 32650925549393271192213089)
        ·
          refine ⟨24488194162044953394159817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32650925549393271192213089 24488194162044953394159817)
          ·
            refine ⟨18366145621533715045619863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24488194162044953394159817 18366145621533715045619863)
            ·
              refine ⟨27549218432300572568429795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18366145621533715045619863 27549218432300572568429795)
              ·
                refine ⟨41323827648450858852644693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27549218432300572568429795 41323827648450858852644693)
                ·
                  refine ⟨242131802627641751089715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 41323827648450858852644693 242131802627641751089715)
                  ·
                    rfl

theorem cell23_4243950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 9].length) (baseStart_4243950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4243950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4243950 prefixEnd_4243950 := by exact prefixLift 4243950
  have htrace : WordTrace (prefixWord ++ tailWord_4243950) baseStart_4243950 baseEnd_4243950 := by
    simpa [prefixWord, tailWord_4243950, baseEnd_4243950] using wordTrace_append hprefix tailTrace_4243950
  have hstable : (prefixWord ++ tailWord_4243950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4243950).length < 2 ^ (prefixWord ++ tailWord_4243950).sum := by decide
  have hdescent : baseEnd_4243950 < baseStart_4243950 := by decide
  rcases family_descends (prefixWord ++ tailWord_4243950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4243960 : List Nat := [2, 1, 2, 1, 1, 4, 1, 2, 1, 5, 3]
def baseStart_4243960 : Nat := 118140960795 + 4243960 * 2 ^ 59
def prefixEnd_4243960 : Nat := 4983230072969 + 3 ^ 40 * 4243960 * 2
def baseEnd_4243960 : Nat := 2179191358455320720682389

theorem tailTrace_4243960 : CollatzResearch.WordTrace tailWord_4243960 prefixEnd_4243960 2179191358455320720682389 := by
  unfold tailWord_4243960
  simp only [CollatzResearch.WordTrace]
  refine ⟨77394968852432602753992667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103193291803243470338656889 77394968852432602753992667)
  ·
    refine ⟨116092453278648904130989001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77394968852432602753992667 116092453278648904130989001)
    ·
      refine ⟨87069339958986678098241751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116092453278648904130989001 87069339958986678098241751)
      ·
        refine ⟨130604009938480017147362627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87069339958986678098241751 130604009938480017147362627)
        ·
          refine ⟨195906014907720025721043941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130604009938480017147362627 195906014907720025721043941)
          ·
            refine ⟨36732377795197504822695739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 195906014907720025721043941 36732377795197504822695739)
            ·
              refine ⟨55098566692796257234043609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36732377795197504822695739 55098566692796257234043609)
              ·
                refine ⟨41323925019597192925532707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55098566692796257234043609 41323925019597192925532707)
                ·
                  refine ⟨61985887529395789388299061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41323925019597192925532707 61985887529395789388299061)
                  ·
                    refine ⟨5811176955880855255153037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61985887529395789388299061 5811176955880855255153037)
                    ·
                      refine ⟨2179191358455320720682389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5811176955880855255153037 2179191358455320720682389)
                      ·
                        rfl

theorem cell23_4243960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 1, 5, 3].length) (baseStart_4243960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4243960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4243960 prefixEnd_4243960 := by exact prefixLift 4243960
  have htrace : WordTrace (prefixWord ++ tailWord_4243960) baseStart_4243960 baseEnd_4243960 := by
    simpa [prefixWord, tailWord_4243960, baseEnd_4243960] using wordTrace_append hprefix tailTrace_4243960
  have hstable : (prefixWord ++ tailWord_4243960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4243960).length < 2 ^ (prefixWord ++ tailWord_4243960).sum := by decide
  have hdescent : baseEnd_4243960 < baseStart_4243960 := by decide
  rcases family_descends (prefixWord ++ tailWord_4243960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4243967 : List Nat := [1, 1, 2, 2, 1, 2, 6, 3, 5]
def baseStart_4243967 : Nat := 118140960795 + 4243967 * 2 ^ 59
def prefixEnd_4243967 : Nat := 4983230072969 + 3 ^ 40 * 4243967 * 2
def baseEnd_4243967 : Nat := 242132772535544688143873

theorem tailTrace_4243967 : CollatzResearch.WordTrace tailWord_4243967 prefixEnd_4243967 242132772535544688143873 := by
  unfold tailWord_4243967
  simp only [CollatzResearch.WordTrace]
  refine ⟨154790193015839845703490155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103193462010559897135660103 154790193015839845703490155)
  ·
    refine ⟨232185289523759768555235233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154790193015839845703490155 232185289523759768555235233)
    ·
      refine ⟨174138967142819826416426425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232185289523759768555235233 174138967142819826416426425)
      ·
        refine ⟨130604225357114869812319819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174138967142819826416426425 130604225357114869812319819)
        ·
          refine ⟨195906338035672304718479729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130604225357114869812319819 195906338035672304718479729)
          ·
            refine ⟨146929753526754228538859797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 195906338035672304718479729 146929753526754228538859797)
            ·
              refine ⟨6887332196566604462759053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 146929753526754228538859797 6887332196566604462759053)
              ·
                refine ⟨2582749573712476673534645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6887332196566604462759053 2582749573712476673534645)
                ·
                  refine ⟨242132772535544688143873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2582749573712476673534645 242132772535544688143873)
                  ·
                    rfl

theorem cell23_4243967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 3, 5].length) (baseStart_4243967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4243967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4243967 prefixEnd_4243967 := by exact prefixLift 4243967
  have htrace : WordTrace (prefixWord ++ tailWord_4243967) baseStart_4243967 baseEnd_4243967 := by
    simpa [prefixWord, tailWord_4243967, baseEnd_4243967] using wordTrace_append hprefix tailTrace_4243967
  have hstable : (prefixWord ++ tailWord_4243967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4243967).length < 2 ^ (prefixWord ++ tailWord_4243967).sum := by decide
  have hdescent : baseEnd_4243967 < baseStart_4243967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4243967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4244017 : List Nat := [1, 2, 2, 3, 1, 1, 2, 2, 1, 6, 2]
def baseStart_4244017 : Nat := 118140960795 + 4244017 * 2 ^ 59
def prefixEnd_4244017 : Nat := 4983230072969 + 3 ^ 40 * 4244017 * 2
def baseEnd_4244017 : Nat := 2179220626852626997669627

theorem tailTrace_4244017 : CollatzResearch.WordTrace tailWord_4244017 prefixEnd_4244017 2179220626852626997669627 := by
  unfold tailWord_4244017
  simp only [CollatzResearch.WordTrace]
  refine ⟨154792016665658704242810305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103194677777105802828540203 154792016665658704242810305)
  ·
    refine ⟨116094012499244028182107729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154792016665658704242810305 116094012499244028182107729)
    ·
      refine ⟨87070509374433021136580797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116094012499244028182107729 87070509374433021136580797)
      ·
        refine ⟨32651441015412382926217799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87070509374433021136580797 32651441015412382926217799)
        ·
          refine ⟨48977161523118574389326699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32651441015412382926217799 48977161523118574389326699)
          ·
            refine ⟨73465742284677861583990049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48977161523118574389326699 73465742284677861583990049)
            ·
              refine ⟨55099306713508396187992537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73465742284677861583990049 55099306713508396187992537)
              ·
                refine ⟨41324480035131297140994403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55099306713508396187992537 41324480035131297140994403)
                ·
                  refine ⟨61986720052696945711491605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41324480035131297140994403 61986720052696945711491605)
                  ·
                    refine ⟨2905627502470169330226169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 61986720052696945711491605 2905627502470169330226169)
                    ·
                      refine ⟨2179220626852626997669627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2905627502470169330226169 2179220626852626997669627)
                      ·
                        rfl

theorem cell23_4244017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 6, 2].length) (baseStart_4244017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4244017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4244017 prefixEnd_4244017 := by exact prefixLift 4244017
  have htrace : WordTrace (prefixWord ++ tailWord_4244017) baseStart_4244017 baseEnd_4244017 := by
    simpa [prefixWord, tailWord_4244017, baseEnd_4244017] using wordTrace_append hprefix tailTrace_4244017
  have hstable : (prefixWord ++ tailWord_4244017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4244017).length < 2 ^ (prefixWord ++ tailWord_4244017).sum := by decide
  have hdescent : baseEnd_4244017 < baseStart_4244017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4244017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4244037 : List Nat := [1, 3, 1, 1, 1, 5, 1, 1, 4, 2, 3]
def baseStart_4244037 : Nat := 118140960795 + 4244037 * 2 ^ 59
def prefixEnd_4244037 : Nat := 4983230072969 + 3 ^ 40 * 4244037 * 2
def baseEnd_4244037 : Nat := 2179230896465716919419535

theorem tailTrace_4244037 : CollatzResearch.WordTrace tailWord_4244037 prefixEnd_4244037 2179230896465716919419535 := by
  unfold tailWord_4244037
  simp only [CollatzResearch.WordTrace]
  refine ⟨154792746125586247658538365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103195164083724165105692243 154792746125586247658538365)
  ·
    refine ⟨58047279797094842871951887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154792746125586247658538365 58047279797094842871951887)
    ·
      refine ⟨87070919695642264307927831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58047279797094842871951887 87070919695642264307927831)
      ·
        refine ⟨130606379543463396461891747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87070919695642264307927831 130606379543463396461891747)
        ·
          refine ⟨195909569315195094692837621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130606379543463396461891747 195909569315195094692837621)
          ·
            refine ⟨18366522123299540127453527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 195909569315195094692837621 18366522123299540127453527)
            ·
              refine ⟨27549783184949310191180291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18366522123299540127453527 27549783184949310191180291)
              ·
                refine ⟨41324674777423965286770437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27549783184949310191180291 41324674777423965286770437)
                ·
                  refine ⟨7748376520766993491269457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41324674777423965286770437 7748376520766993491269457)
                  ·
                    refine ⟨5811282390575245118452093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7748376520766993491269457 5811282390575245118452093)
                    ·
                      refine ⟨2179230896465716919419535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5811282390575245118452093 2179230896465716919419535)
                      ·
                        rfl

theorem cell23_4244037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 4, 2, 3].length) (baseStart_4244037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4244037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4244037 prefixEnd_4244037 := by exact prefixLift 4244037
  have htrace : WordTrace (prefixWord ++ tailWord_4244037) baseStart_4244037 baseEnd_4244037 := by
    simpa [prefixWord, tailWord_4244037, baseEnd_4244037] using wordTrace_append hprefix tailTrace_4244037
  have hstable : (prefixWord ++ tailWord_4244037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4244037).length < 2 ^ (prefixWord ++ tailWord_4244037).sum := by decide
  have hdescent : baseEnd_4244037 < baseStart_4244037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4244037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4244087 : List Nat := [1, 1, 3, 1, 1, 3, 2, 5, 1, 5]
def baseStart_4244087 : Nat := 118140960795 + 4244087 * 2 ^ 59
def prefixEnd_4244087 : Nat := 4983230072969 + 3 ^ 40 * 4244087 * 2
def baseEnd_4244087 : Nat := 726418856832813907931435

theorem tailTrace_4244087 : CollatzResearch.WordTrace tailWord_4244087 prefixEnd_4244087 726418856832813907931435 := by
  unfold tailWord_4244087
  simp only [CollatzResearch.WordTrace]
  refine ⟨154794569775405106197858515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103196379850270070798572343 154794569775405106197858515)
  ·
    refine ⟨232191854663107659296787773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154794569775405106197858515 232191854663107659296787773)
    ·
      refine ⟨87071945498665372236295415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 232191854663107659296787773 87071945498665372236295415)
      ·
        refine ⟨130607918247998058354443123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87071945498665372236295415 130607918247998058354443123)
        ·
          refine ⟨195911877371997087531664685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130607918247998058354443123 195911877371997087531664685)
          ·
            refine ⟨73466954014498907824374257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 195911877371997087531664685 73466954014498907824374257)
            ·
              refine ⟨55100215510874180868280693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73466954014498907824374257 55100215510874180868280693)
              ·
                refine ⟨5165645204144454456401315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55100215510874180868280693 5165645204144454456401315)
                ·
                  refine ⟨7748467806216681684601973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5165645204144454456401315 7748467806216681684601973)
                  ·
                    refine ⟨726418856832813907931435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7748467806216681684601973 726418856832813907931435)
                    ·
                      rfl

theorem cell23_4244087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 5, 1, 5].length) (baseStart_4244087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4244087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4244087 prefixEnd_4244087 := by exact prefixLift 4244087
  have htrace : WordTrace (prefixWord ++ tailWord_4244087) baseStart_4244087 baseEnd_4244087 := by
    simpa [prefixWord, tailWord_4244087, baseEnd_4244087] using wordTrace_append hprefix tailTrace_4244087
  have hstable : (prefixWord ++ tailWord_4244087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4244087).length < 2 ^ (prefixWord ++ tailWord_4244087).sum := by decide
  have hdescent : baseEnd_4244087 < baseStart_4244087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4244087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4244117 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 8, 4]
def baseStart_4244117 : Nat := 118140960795 + 4244117 * 2 ^ 59
def prefixEnd_4244117 : Nat := 4983230072969 + 3 ^ 40 * 4244117 * 2
def baseEnd_4244117 : Nat := 726423991639358868806389

theorem tailTrace_4244117 : CollatzResearch.WordTrace tailWord_4244117 prefixEnd_4244117 726423991639358868806389 := by
  unfold tailWord_4244117
  simp only [CollatzResearch.WordTrace]
  refine ⟨154795663965296421321450605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103197109310197614214300403 154795663965296421321450605)
  ·
    refine ⟨58048373986986157995543977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154795663965296421321450605 58048373986986157995543977)
    ·
      refine ⟨43536280490239618496657983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58048373986986157995543977 43536280490239618496657983)
      ·
        refine ⟨65304420735359427744986975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43536280490239618496657983 65304420735359427744986975)
        ·
          refine ⟨97956631103039141617480463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65304420735359427744986975 97956631103039141617480463)
          ·
            refine ⟨146934946654558712426220695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97956631103039141617480463 146934946654558712426220695)
            ·
              refine ⟨220402419981838068639331043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146934946654558712426220695 220402419981838068639331043)
              ·
                refine ⟨330603629972757102958996565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 220402419981838068639331043 330603629972757102958996565)
                ·
                  refine ⟨3874261288743247300300741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 330603629972757102958996565 3874261288743247300300741)
                  ·
                    refine ⟨726423991639358868806389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3874261288743247300300741 726423991639358868806389)
                    ·
                      rfl

theorem cell23_4244117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 8, 4].length) (baseStart_4244117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4244117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4244117 prefixEnd_4244117 := by exact prefixLift 4244117
  have htrace : WordTrace (prefixWord ++ tailWord_4244117) baseStart_4244117 baseEnd_4244117 := by
    simpa [prefixWord, tailWord_4244117, baseEnd_4244117] using wordTrace_append hprefix tailTrace_4244117
  have hstable : (prefixWord ++ tailWord_4244117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4244117).length < 2 ^ (prefixWord ++ tailWord_4244117).sum := by decide
  have hdescent : baseEnd_4244117 < baseStart_4244117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4244117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4244124 : List Nat := [2, 2, 3, 2, 2, 1, 2, 1, 3, 1, 4]
def baseStart_4244124 : Nat := 118140960795 + 4244124 * 2 ^ 59
def prefixEnd_4244124 : Nat := 4983230072969 + 3 ^ 40 * 4244124 * 2
def baseEnd_4244124 : Nat := 2179275569282658079031635

theorem tailTrace_4244124 : CollatzResearch.WordTrace tailWord_4244124 prefixEnd_4244124 2179275569282658079031635 := by
  unfold tailWord_4244124
  simp only [CollatzResearch.WordTrace]
  refine ⟨77397959638135530758477713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103197279517514041011303617 77397959638135530758477713)
  ·
    refine ⟨58048469728601648068858285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77397959638135530758477713 58048469728601648068858285)
    ·
      refine ⟨21768176148225618025821857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58048469728601648068858285 21768176148225618025821857)
      ·
        refine ⟨16326132111169213519366393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21768176148225618025821857 16326132111169213519366393)
        ·
          refine ⟨12244599083376910139524795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16326132111169213519366393 12244599083376910139524795)
          ·
            refine ⟨18366898625065365209287193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12244599083376910139524795 18366898625065365209287193)
            ·
              refine ⟨13775173968799023906965395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18366898625065365209287193 13775173968799023906965395)
              ·
                refine ⟨20662760953198535860448093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13775173968799023906965395 20662760953198535860448093)
                ·
                  refine ⟨7748535357449450947668035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20662760953198535860448093 7748535357449450947668035)
                  ·
                    refine ⟨11622803036174176421502053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7748535357449450947668035 11622803036174176421502053)
                    ·
                      refine ⟨2179275569282658079031635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11622803036174176421502053 2179275569282658079031635)
                      ·
                        rfl

theorem cell23_4244124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_4244124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4244124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4244124 prefixEnd_4244124 := by exact prefixLift 4244124
  have htrace : WordTrace (prefixWord ++ tailWord_4244124) baseStart_4244124 baseEnd_4244124 := by
    simpa [prefixWord, tailWord_4244124, baseEnd_4244124] using wordTrace_append hprefix tailTrace_4244124
  have hstable : (prefixWord ++ tailWord_4244124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4244124).length < 2 ^ (prefixWord ++ tailWord_4244124).sum := by decide
  have hdescent : baseEnd_4244124 < baseStart_4244124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4244124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4244128 : List Nat := [2, 1, 1, 4, 4, 2, 1, 1, 2, 3, 2]
def baseStart_4244128 : Nat := 118140960795 + 4244128 * 2 ^ 59
def prefixEnd_4244128 : Nat := 4983230072969 + 3 ^ 40 * 4244128 * 2
def baseEnd_4244128 : Nat := 2179277623205276063381617

theorem tailTrace_4244128 : CollatzResearch.WordTrace tailWord_4244128 prefixEnd_4244128 2179277623205276063381617 := by
  unfold tailWord_4244128
  simp only [CollatzResearch.WordTrace]
  refine ⟨77398032584128285100050519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103197376778837713466734025 77398032584128285100050519)
  ·
    refine ⟨116097048876192427650075779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77398032584128285100050519 116097048876192427650075779)
    ·
      refine ⟨174145573314288641475113669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116097048876192427650075779 174145573314288641475113669)
      ·
        refine ⟨32652294996429120276583813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 174145573314288641475113669 32652294996429120276583813)
        ·
          refine ⟨6122305311830460051859465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32652294996429120276583813 6122305311830460051859465)
          ·
            refine ⟨4591728983872845038894599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6122305311830460051859465 4591728983872845038894599)
            ·
              refine ⟨6887593475809267558341899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4591728983872845038894599 6887593475809267558341899)
              ·
                refine ⟨10331390213713901337512849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6887593475809267558341899 10331390213713901337512849)
                ·
                  refine ⟨7748542660285426003134637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10331390213713901337512849 7748542660285426003134637)
                  ·
                    refine ⟨2905703497607034751175489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7748542660285426003134637 2905703497607034751175489)
                    ·
                      refine ⟨2179277623205276063381617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2905703497607034751175489 2179277623205276063381617)
                      ·
                        rfl

theorem cell23_4244128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 2, 3, 2].length) (baseStart_4244128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4244128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4244128 prefixEnd_4244128 := by exact prefixLift 4244128
  have htrace : WordTrace (prefixWord ++ tailWord_4244128) baseStart_4244128 baseEnd_4244128 := by
    simpa [prefixWord, tailWord_4244128, baseEnd_4244128] using wordTrace_append hprefix tailTrace_4244128
  have hstable : (prefixWord ++ tailWord_4244128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4244128).length < 2 ^ (prefixWord ++ tailWord_4244128).sum := by decide
  have hdescent : baseEnd_4244128 < baseStart_4244128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4244128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4244138 : List Nat := [3, 1, 5, 2, 1, 1, 1, 3, 1, 5]
def baseStart_4244138 : Nat := 118140960795 + 4244138 * 2 ^ 59
def prefixEnd_4244138 : Nat := 4983230072969 + 3 ^ 40 * 4244138 * 2
def baseEnd_4244138 : Nat := 726427586003940341418857

theorem tailTrace_4244138 : CollatzResearch.WordTrace tailWord_4244138 prefixEnd_4244138 726427586003940341418857 := by
  unfold tailWord_4244138
  simp only [CollatzResearch.WordTrace]
  refine ⟨38699107474555085476991267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103197619932146894605310045 38699107474555085476991267)
  ·
    refine ⟨58048661211832628215486901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38699107474555085476991267 58048661211832628215486901)
    ·
      refine ⟨5442061988609308895201897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58048661211832628215486901 5442061988609308895201897)
      ·
        refine ⟨4081546491456981671401423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5442061988609308895201897 4081546491456981671401423)
        ·
          refine ⟨6122319737185472507102135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4081546491456981671401423 6122319737185472507102135)
          ·
            refine ⟨9183479605778208760653203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6122319737185472507102135 9183479605778208760653203)
            ·
              refine ⟨13775219408667313140979805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9183479605778208760653203 13775219408667313140979805)
              ·
                refine ⟨5165707278250242427867427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13775219408667313140979805 5165707278250242427867427)
                ·
                  refine ⟨7748560917375363641801141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5165707278250242427867427 7748560917375363641801141)
                  ·
                    refine ⟨726427586003940341418857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7748560917375363641801141 726427586003940341418857)
                    ·
                      rfl

theorem cell23_4244138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_4244138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4244138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4244138 prefixEnd_4244138 := by exact prefixLift 4244138
  have htrace : WordTrace (prefixWord ++ tailWord_4244138) baseStart_4244138 baseEnd_4244138 := by
    simpa [prefixWord, tailWord_4244138, baseEnd_4244138] using wordTrace_append hprefix tailTrace_4244138
  have hstable : (prefixWord ++ tailWord_4244138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4244138).length < 2 ^ (prefixWord ++ tailWord_4244138).sum := by decide
  have hdescent : baseEnd_4244138 < baseStart_4244138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4244138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4244141 : List Nat := [1, 5, 2, 1, 1, 3, 1, 3, 1, 1, 4]
def baseStart_4244141 : Nat := 118140960795 + 4244141 * 2 ^ 59
def prefixEnd_4244141 : Nat := 4983230072969 + 3 ^ 40 * 4244141 * 2
def baseEnd_4244141 : Nat := 2179284298453784512519057

theorem tailTrace_4244141 : CollatzResearch.WordTrace tailWord_4244141 prefixEnd_4244141 2179284298453784512519057 := by
  unfold tailWord_4244141
  simp only [CollatzResearch.WordTrace]
  refine ⟨154796539317209473420324277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103197692878139648946882851 154796539317209473420324277)
  ·
    refine ⟨14512175560988388133155401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 154796539317209473420324277 14512175560988388133155401)
    ·
      refine ⟨10884131670741291099866551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14512175560988388133155401 10884131670741291099866551)
      ·
        refine ⟨16326197506111936649799827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10884131670741291099866551 16326197506111936649799827)
        ·
          refine ⟨24489296259167904974699741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16326197506111936649799827 24489296259167904974699741)
          ·
            refine ⟨9183486097187964365512403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24489296259167904974699741 9183486097187964365512403)
            ·
              refine ⟨13775229145781946548268605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9183486097187964365512403 13775229145781946548268605)
              ·
                refine ⟨5165710929668229955600727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13775229145781946548268605 5165710929668229955600727)
                ·
                  refine ⟨7748566394502344933401091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5165710929668229955600727 7748566394502344933401091)
                  ·
                    refine ⟨11622849591753517400101637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7748566394502344933401091 11622849591753517400101637)
                    ·
                      refine ⟨2179284298453784512519057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11622849591753517400101637 2179284298453784512519057)
                      ·
                        rfl

theorem cell23_4244141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_4244141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4244141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4244141 prefixEnd_4244141 := by exact prefixLift 4244141
  have htrace : WordTrace (prefixWord ++ tailWord_4244141) baseStart_4244141 baseEnd_4244141 := by
    simpa [prefixWord, tailWord_4244141, baseEnd_4244141] using wordTrace_append hprefix tailTrace_4244141
  have hstable : (prefixWord ++ tailWord_4244141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4244141).length < 2 ^ (prefixWord ++ tailWord_4244141).sum := by decide
  have hdescent : baseEnd_4244141 < baseStart_4244141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4244141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4244158 : List Nat := [4, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2]
def baseStart_4244158 : Nat := 118140960795 + 4244158 * 2 ^ 59
def prefixEnd_4244158 : Nat := 4983230072969 + 3 ^ 40 * 4244158 * 2
def baseEnd_4244158 : Nat := 2179293027624910946006479

theorem tailTrace_4244158 : CollatzResearch.WordTrace tailWord_4244158 prefixEnd_4244158 2179293027624910946006479 := by
  unfold tailWord_4244158
  simp only [CollatzResearch.WordTrace]
  refine ⟨19349644919768485665461641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103198106238765256882462085 19349644919768485665461641)
  ·
    refine ⟨14512233689826364249096231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19349644919768485665461641 14512233689826364249096231)
    ·
      refine ⟨21768350534739546373644347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14512233689826364249096231 21768350534739546373644347)
      ·
        refine ⟨32652525802109319560466521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21768350534739546373644347 32652525802109319560466521)
        ·
          refine ⟨24489394351581989670349891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32652525802109319560466521 24489394351581989670349891)
          ·
            refine ⟨36734091527372984505524837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24489394351581989670349891 36734091527372984505524837)
            ·
              refine ⟨6887642161382434594785907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36734091527372984505524837 6887642161382434594785907)
              ·
                refine ⟨10331463242073651892178861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6887642161382434594785907 10331463242073651892178861)
                ·
                  refine ⟨3874298715777619459567073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10331463242073651892178861 3874298715777619459567073)
                  ·
                    refine ⟨2905724036833214594675305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3874298715777619459567073 2905724036833214594675305)
                    ·
                      refine ⟨2179293027624910946006479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2905724036833214594675305 2179293027624910946006479)
                      ·
                        rfl

theorem cell23_4244158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2].length) (baseStart_4244158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4244158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4244158 prefixEnd_4244158 := by exact prefixLift 4244158
  have htrace : WordTrace (prefixWord ++ tailWord_4244158) baseStart_4244158 baseEnd_4244158 := by
    simpa [prefixWord, tailWord_4244158, baseEnd_4244158] using wordTrace_append hprefix tailTrace_4244158
  have hstable : (prefixWord ++ tailWord_4244158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4244158).length < 2 ^ (prefixWord ++ tailWord_4244158).sum := by decide
  have hdescent : baseEnd_4244158 < baseStart_4244158 := by decide
  rcases family_descends (prefixWord ++ tailWord_4244158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4244178 : List Nat := [3, 2, 2, 2, 3, 1, 2, 2, 1, 2, 3]
def baseStart_4244178 : Nat := 118140960795 + 4244178 * 2 ^ 59
def prefixEnd_4244178 : Nat := 4983230072969 + 3 ^ 40 * 4244178 * 2
def baseEnd_4244178 : Nat := 2179303297238000867756387

theorem tailTrace_4244178 : CollatzResearch.WordTrace tailWord_4244178 prefixEnd_4244178 2179303297238000867756387 := by
  unfold tailWord_4244178
  simp only [CollatzResearch.WordTrace]
  refine ⟨38699472204518857184855297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103198592545383619159614125 38699472204518857184855297)
  ·
    refine ⟨29024604153389142888641473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38699472204518857184855297 29024604153389142888641473)
    ·
      refine ⟨21768453115041857166481105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29024604153389142888641473 21768453115041857166481105)
      ·
        refine ⟨16326339836281392874860829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21768453115041857166481105 16326339836281392874860829)
        ·
          refine ⟨6122377438605522328072811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16326339836281392874860829 6122377438605522328072811)
          ·
            refine ⟨9183566157908283492109217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6122377438605522328072811 9183566157908283492109217)
            ·
              refine ⟨6887674618431212619081913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9183566157908283492109217 6887674618431212619081913)
              ·
                refine ⟨5165755963823409464311435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6887674618431212619081913 5165755963823409464311435)
                ·
                  refine ⟨7748633945735114196467153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5165755963823409464311435 7748633945735114196467153)
                  ·
                    refine ⟨5811475459301335647350365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7748633945735114196467153 5811475459301335647350365)
                    ·
                      refine ⟨2179303297238000867756387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5811475459301335647350365 2179303297238000867756387)
                      ·
                        rfl

theorem cell23_4244178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_4244178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4244178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4244178 prefixEnd_4244178 := by exact prefixLift 4244178
  have htrace : WordTrace (prefixWord ++ tailWord_4244178) baseStart_4244178 baseEnd_4244178 := by
    simpa [prefixWord, tailWord_4244178, baseEnd_4244178] using wordTrace_append hprefix tailTrace_4244178
  have hstable : (prefixWord ++ tailWord_4244178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4244178).length < 2 ^ (prefixWord ++ tailWord_4244178).sum := by decide
  have hdescent : baseEnd_4244178 < baseStart_4244178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4244178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4244201 : List Nat := [1, 2, 1, 1, 1, 2, 6, 3, 1, 3, 2]
def baseStart_4244201 : Nat := 118140960795 + 4244201 * 2 ^ 59
def prefixEnd_4244201 : Nat := 4983230072969 + 3 ^ 40 * 4244201 * 2
def baseEnd_4244201 : Nat := 2179315107293054277768781

theorem tailTrace_4244201 : CollatzResearch.WordTrace tailWord_4244201 prefixEnd_4244201 2179315107293054277768781 := by
  unfold tailWord_4244201
  simp only [CollatzResearch.WordTrace]
  refine ⟨154798727696992103667508457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103199151797994735778338971 154798727696992103667508457)
  ·
    refine ⟨116099045772744077750631343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154798727696992103667508457 116099045772744077750631343)
    ·
      refine ⟨174148568659116116625947015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116099045772744077750631343 174148568659116116625947015)
      ·
        refine ⟨261222852988674174938920523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174148568659116116625947015 261222852988674174938920523)
        ·
          refine ⟨391834279483011262408380785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261222852988674174938920523 391834279483011262408380785)
          ·
            refine ⟨293875709612258446806285589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 391834279483011262408380785 293875709612258446806285589)
            ·
              refine ⟨13775423888074614694044637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 293875709612258446806285589 13775423888074614694044637)
              ·
                refine ⟨5165783958027980510266739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13775423888074614694044637 5165783958027980510266739)
                ·
                  refine ⟨7748675937041970765400109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5165783958027980510266739 7748675937041970765400109)
                  ·
                    refine ⟨2905753476390739037025041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7748675937041970765400109 2905753476390739037025041)
                    ·
                      refine ⟨2179315107293054277768781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2905753476390739037025041 2179315107293054277768781)
                      ·
                        rfl

theorem cell23_4244201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 3, 1, 3, 2].length) (baseStart_4244201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4244201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4244201 prefixEnd_4244201 := by exact prefixLift 4244201
  have htrace : WordTrace (prefixWord ++ tailWord_4244201) baseStart_4244201 baseEnd_4244201 := by
    simpa [prefixWord, tailWord_4244201, baseEnd_4244201] using wordTrace_append hprefix tailTrace_4244201
  have hstable : (prefixWord ++ tailWord_4244201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4244201).length < 2 ^ (prefixWord ++ tailWord_4244201).sum := by decide
  have hdescent : baseEnd_4244201 < baseStart_4244201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4244201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4244214 : List Nat := [5, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4]
def baseStart_4244214 : Nat := 118140960795 + 4244214 * 2 ^ 59
def prefixEnd_4244214 : Nat := 4983230072969 + 3 ^ 40 * 4244214 * 2
def baseEnd_4244214 : Nat := 2179321782541562726906221

theorem tailTrace_4244214 : CollatzResearch.WordTrace tailWord_4244214 prefixEnd_4244214 2179321782541562726906221 := by
  unfold tailWord_4244214
  simp only [CollatzResearch.WordTrace]
  refine ⟨9674950115371562930483231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 103199467897296671258487797 9674950115371562930483231)
  ·
    refine ⟨14512425173057344395724847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9674950115371562930483231 14512425173057344395724847)
    ·
      refine ⟨21768637759586016593587271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14512425173057344395724847 21768637759586016593587271)
      ·
        refine ⟨32652956639379024890380907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21768637759586016593587271 32652956639379024890380907)
        ·
          refine ⟨48979434959068537335571361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32652956639379024890380907 48979434959068537335571361)
          ·
            refine ⟨36734576219301403001678521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48979434959068537335571361 36734576219301403001678521)
            ·
              refine ⟨27550932164476052251258891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36734576219301403001678521 27550932164476052251258891)
              ·
                refine ⟨41326398246714078376888337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27550932164476052251258891 41326398246714078376888337)
                ·
                  refine ⟨30994798685035558782666253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41326398246714078376888337 30994798685035558782666253)
                  ·
                    refine ⟨11623049506888334543499845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30994798685035558782666253 11623049506888334543499845)
                    ·
                      refine ⟨2179321782541562726906221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11623049506888334543499845 2179321782541562726906221)
                      ·
                        rfl

theorem cell23_4244214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_4244214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4244214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4244214 prefixEnd_4244214 := by exact prefixLift 4244214
  have htrace : WordTrace (prefixWord ++ tailWord_4244214) baseStart_4244214 baseEnd_4244214 := by
    simpa [prefixWord, tailWord_4244214, baseEnd_4244214] using wordTrace_append hprefix tailTrace_4244214
  have hstable : (prefixWord ++ tailWord_4244214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4244214).length < 2 ^ (prefixWord ++ tailWord_4244214).sum := by decide
  have hdescent : baseEnd_4244214 < baseStart_4244214 := by decide
  rcases family_descends (prefixWord ++ tailWord_4244214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4244227 : List Nat := [1, 1, 1, 3, 2, 2, 1, 3, 1, 4, 4]
def baseStart_4244227 : Nat := 118140960795 + 4244227 * 2 ^ 59
def prefixEnd_4244227 : Nat := 4983230072969 + 3 ^ 40 * 4244227 * 2
def baseEnd_4244227 : Nat := 2179328457790071176043661

theorem tailTrace_4244227 : CollatzResearch.WordTrace tailWord_4244227 prefixEnd_4244227 2179328457790071176043661 := by
  unfold tailWord_4244227
  simp only [CollatzResearch.WordTrace]
  refine ⟨154799675994897910107954935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103199783996598606738636623 154799675994897910107954935)
  ·
    refine ⟨232199513992346865161932403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154799675994897910107954935 232199513992346865161932403)
    ·
      refine ⟨348299270988520297742898605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232199513992346865161932403 348299270988520297742898605)
      ·
        refine ⟨130612226620695111653586977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 348299270988520297742898605 130612226620695111653586977)
        ·
          refine ⟨97959169965521333740190233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130612226620695111653586977 97959169965521333740190233)
          ·
            refine ⟨73469377474141000305142675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97959169965521333740190233 73469377474141000305142675)
            ·
              refine ⟨110204066211211500457714013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73469377474141000305142675 110204066211211500457714013)
              ·
                refine ⟨41326524829204312671642755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110204066211211500457714013 41326524829204312671642755)
                ·
                  refine ⟨61989787243806469007464133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41326524829204312671642755 61989787243806469007464133)
                  ·
                    refine ⟨11623085108213712938899525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61989787243806469007464133 11623085108213712938899525)
                    ·
                      refine ⟨2179328457790071176043661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11623085108213712938899525 2179328457790071176043661)
                      ·
                        rfl

theorem cell23_4244227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 4, 4].length) (baseStart_4244227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4244227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4244227 prefixEnd_4244227 := by exact prefixLift 4244227
  have htrace : WordTrace (prefixWord ++ tailWord_4244227) baseStart_4244227 baseEnd_4244227 := by
    simpa [prefixWord, tailWord_4244227, baseEnd_4244227] using wordTrace_append hprefix tailTrace_4244227
  have hstable : (prefixWord ++ tailWord_4244227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4244227).length < 2 ^ (prefixWord ++ tailWord_4244227).sum := by decide
  have hdescent : baseEnd_4244227 < baseStart_4244227 := by decide
  rcases family_descends (prefixWord ++ tailWord_4244227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4244278 : List Nat := [5, 1, 2, 2, 2, 1, 1, 1, 2, 2, 4]
def baseStart_4244278 : Nat := 118140960795 + 4244278 * 2 ^ 59
def prefixEnd_4244278 : Nat := 4983230072969 + 3 ^ 40 * 4244278 * 2
def baseEnd_4244278 : Nat := 2179354645303450476505927

theorem tailTrace_4244278 : CollatzResearch.WordTrace tailWord_4244278 prefixEnd_4244278 2179354645303450476505927 := by
  unfold tailWord_4244278
  simp only [CollatzResearch.WordTrace]
  refine ⟨9675096007357071613628843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 103201024078475430545374325 9675096007357071613628843)
  ·
    refine ⟨14512644011035607420443265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9675096007357071613628843 14512644011035607420443265)
    ·
      refine ⟨10884483008276705565332449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14512644011035607420443265 10884483008276705565332449)
      ·
        refine ⟨8163362256207529173999337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10884483008276705565332449 8163362256207529173999337)
        ·
          refine ⟨6122521692155646880499503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8163362256207529173999337 6122521692155646880499503)
          ·
            refine ⟨9183782538233470320749255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6122521692155646880499503 9183782538233470320749255)
            ·
              refine ⟨13775673807350205481123883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9183782538233470320749255 13775673807350205481123883)
              ·
                refine ⟨20663510711025308221685825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13775673807350205481123883 20663510711025308221685825)
                ·
                  refine ⟨15497633033268981166264369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20663510711025308221685825 15497633033268981166264369)
                  ·
                    refine ⟨11623224774951735874698277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15497633033268981166264369 11623224774951735874698277)
                    ·
                      refine ⟨2179354645303450476505927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11623224774951735874698277 2179354645303450476505927)
                      ·
                        rfl

theorem cell23_4244278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_4244278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4244278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4244278 prefixEnd_4244278 := by exact prefixLift 4244278
  have htrace : WordTrace (prefixWord ++ tailWord_4244278) baseStart_4244278 baseEnd_4244278 := by
    simpa [prefixWord, tailWord_4244278, baseEnd_4244278] using wordTrace_append hprefix tailTrace_4244278
  have hstable : (prefixWord ++ tailWord_4244278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4244278).length < 2 ^ (prefixWord ++ tailWord_4244278).sum := by decide
  have hdescent : baseEnd_4244278 < baseStart_4244278 := by decide
  rcases family_descends (prefixWord ++ tailWord_4244278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4244341 : List Nat := [1, 3, 4, 1, 1, 2, 1, 2, 1, 4, 3]
def baseStart_4244341 : Nat := 118140960795 + 4244341 * 2 ^ 59
def prefixEnd_4244341 : Nat := 4983230072969 + 3 ^ 40 * 4244341 * 2
def baseEnd_4244341 : Nat := 2179386994584683730018137

theorem tailTrace_4244341 : CollatzResearch.WordTrace tailWord_4244341 prefixEnd_4244341 2179386994584683730018137 := by
  unfold tailWord_4244341
  simp only [CollatzResearch.WordTrace]
  refine ⟨154803833916484907577604877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103202555944323271718403251 154803833916484907577604877)
  ·
    refine ⟨58051437718681840341601829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154803833916484907577604877 58051437718681840341601829)
    ·
      refine ⟨10884644572252845064050343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58051437718681840341601829 10884644572252845064050343)
      ·
        refine ⟨16326966858379267596075515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10884644572252845064050343 16326966858379267596075515)
        ·
          refine ⟨24490450287568901394113273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16326966858379267596075515 24490450287568901394113273)
          ·
            refine ⟨18367837715676676045584955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24490450287568901394113273 18367837715676676045584955)
            ·
              refine ⟨27551756573515014068377433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18367837715676676045584955 27551756573515014068377433)
              ·
                refine ⟨20663817430136260551283075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27551756573515014068377433 20663817430136260551283075)
                ·
                  refine ⟨30995726145204390826924613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20663817430136260551283075 30995726145204390826924613)
                  ·
                    refine ⟨5811698652225823280048365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30995726145204390826924613 5811698652225823280048365)
                    ·
                      refine ⟨2179386994584683730018137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5811698652225823280048365 2179386994584683730018137)
                      ·
                        rfl

theorem cell23_4244341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_4244341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4244341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4244341 prefixEnd_4244341 := by exact prefixLift 4244341
  have htrace : WordTrace (prefixWord ++ tailWord_4244341) baseStart_4244341 baseEnd_4244341 := by
    simpa [prefixWord, tailWord_4244341, baseEnd_4244341] using wordTrace_append hprefix tailTrace_4244341
  have hstable : (prefixWord ++ tailWord_4244341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4244341).length < 2 ^ (prefixWord ++ tailWord_4244341).sum := by decide
  have hdescent : baseEnd_4244341 < baseStart_4244341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4244341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4244408 : List Nat := [2, 1, 2, 1, 2, 6, 1, 2, 1, 5]
def baseStart_4244408 : Nat := 118140960795 + 4244408 * 2 ^ 59
def prefixEnd_4244408 : Nat := 4983230072969 + 3 ^ 40 * 4244408 * 2
def baseEnd_4244408 : Nat := 726473799262844989293443

theorem tailTrace_4244408 : CollatzResearch.WordTrace tailWord_4244408 prefixEnd_4244408 726473799262844989293443 := by
  unfold tailWord_4244408
  simp only [CollatzResearch.WordTrace]
  refine ⟨77403138803621089010146939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103204185071494785346862585 77403138803621089010146939)
  ·
    refine ⟨116104708205431633515220409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77403138803621089010146939 116104708205431633515220409)
    ·
      refine ⟨87078531154073725136415307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116104708205431633515220409 87078531154073725136415307)
      ·
        refine ⟨130617796731110587704622961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87078531154073725136415307 130617796731110587704622961)
        ·
          refine ⟨97963347548332940778467221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130617796731110587704622961 97963347548332940778467221)
          ·
            refine ⟨4592031916328106598990651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 97963347548332940778467221 4592031916328106598990651)
            ·
              refine ⟨6888047874492159898485977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4592031916328106598990651 6888047874492159898485977)
              ·
                refine ⟨5166035905869119923864483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6888047874492159898485977 5166035905869119923864483)
                ·
                  refine ⟨7749053858803679885796725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5166035905869119923864483 7749053858803679885796725)
                  ·
                    refine ⟨726473799262844989293443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7749053858803679885796725 726473799262844989293443)
                    ·
                      rfl

theorem cell23_4244408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 2, 1, 5].length) (baseStart_4244408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4244408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4244408 prefixEnd_4244408 := by exact prefixLift 4244408
  have htrace : WordTrace (prefixWord ++ tailWord_4244408) baseStart_4244408 baseEnd_4244408 := by
    simpa [prefixWord, tailWord_4244408, baseEnd_4244408] using wordTrace_append hprefix tailTrace_4244408
  have hstable : (prefixWord ++ tailWord_4244408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4244408).length < 2 ^ (prefixWord ++ tailWord_4244408).sum := by decide
  have hdescent : baseEnd_4244408 < baseStart_4244408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4244408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4244431 : List Nat := [1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 5]
def baseStart_4244431 : Nat := 118140960795 + 4244431 * 2 ^ 59
def prefixEnd_4244431 : Nat := 4983230072969 + 3 ^ 40 * 4244431 * 2
def baseEnd_4244431 : Nat := 2179433207843588377892723

theorem tailTrace_4244431 : CollatzResearch.WordTrace tailWord_4244431 prefixEnd_4244431 2179433207843588377892723 := by
  unfold tailWord_4244431
  simp only [CollatzResearch.WordTrace]
  refine ⟨154807116486158852948381147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103204744324105901965587431 154807116486158852948381147)
  ·
    refine ⟨232210674729238279422571721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154807116486158852948381147 232210674729238279422571721)
    ·
      refine ⟨174158006046928709566928791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232210674729238279422571721 174158006046928709566928791)
      ·
        refine ⟨261237009070393064350393187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174158006046928709566928791 261237009070393064350393187)
        ·
          refine ⟨391855513605589596525589781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261237009070393064350393187 391855513605589596525589781)
          ·
            refine ⟨18368227200262012337137021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 391855513605589596525589781 18368227200262012337137021)
            ·
              refine ⟨6888085200098254626426383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18368227200262012337137021 6888085200098254626426383)
              ·
                refine ⟨10332127800147381939639575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6888085200098254626426383 10332127800147381939639575)
                ·
                  refine ⟨15498191700221072909459363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10332127800147381939639575 15498191700221072909459363)
                  ·
                    refine ⟨23247287550331609364189045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15498191700221072909459363 23247287550331609364189045)
                    ·
                      refine ⟨2179433207843588377892723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23247287550331609364189045 2179433207843588377892723)
                      ·
                        rfl

theorem cell23_4244431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 5].length) (baseStart_4244431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4244431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4244431 prefixEnd_4244431 := by exact prefixLift 4244431
  have htrace : WordTrace (prefixWord ++ tailWord_4244431) baseStart_4244431 baseEnd_4244431 := by
    simpa [prefixWord, tailWord_4244431, baseEnd_4244431] using wordTrace_append hprefix tailTrace_4244431
  have hstable : (prefixWord ++ tailWord_4244431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4244431).length < 2 ^ (prefixWord ++ tailWord_4244431).sum := by decide
  have hdescent : baseEnd_4244431 < baseStart_4244431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4244431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4244458 : List Nat := [3, 1, 3, 1, 2, 3, 2, 1, 1, 2, 4]
def baseStart_4244458 : Nat := 118140960795 + 4244458 * 2 ^ 59
def prefixEnd_4244458 : Nat := 4983230072969 + 3 ^ 40 * 4244458 * 2
def baseEnd_4244458 : Nat := 2179447071821259772255099

theorem tailTrace_4244458 : CollatzResearch.WordTrace tailWord_4244458 prefixEnd_4244458 2179447071821259772255099 := by
  unfold tailWord_4244458
  simp only [CollatzResearch.WordTrace]
  refine ⟨38702025314265259139903507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103205400838040691039742685 38702025314265259139903507)
  ·
    refine ⟨58053037971397888709855261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38702025314265259139903507 58053037971397888709855261)
    ·
      refine ⟨21769889239274208266195723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58053037971397888709855261 21769889239274208266195723)
      ·
        refine ⟨32654833858911312399293585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21769889239274208266195723 32654833858911312399293585)
        ·
          refine ⟨24491125394183484299470189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32654833858911312399293585 24491125394183484299470189)
          ·
            refine ⟨9184172022818806612301321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24491125394183484299470189 9184172022818806612301321)
            ·
              refine ⟨6888129017114104959225991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9184172022818806612301321 6888129017114104959225991)
              ·
                refine ⟨10332193525671157438838987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6888129017114104959225991 10332193525671157438838987)
                ·
                  refine ⟨15498290288506736158258481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10332193525671157438838987 15498290288506736158258481)
                  ·
                    refine ⟨11623717716380052118693861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15498290288506736158258481 11623717716380052118693861)
                    ·
                      refine ⟨2179447071821259772255099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11623717716380052118693861 2179447071821259772255099)
                      ·
                        rfl

theorem cell23_4244458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_4244458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4244458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4244458 prefixEnd_4244458 := by exact prefixLift 4244458
  have htrace : WordTrace (prefixWord ++ tailWord_4244458) baseStart_4244458 baseEnd_4244458 := by
    simpa [prefixWord, tailWord_4244458, baseEnd_4244458] using wordTrace_append hprefix tailTrace_4244458
  have hstable : (prefixWord ++ tailWord_4244458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4244458).length < 2 ^ (prefixWord ++ tailWord_4244458).sum := by decide
  have hdescent : baseEnd_4244458 < baseStart_4244458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4244458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4244462 : List Nat := [4, 1, 2, 1, 4, 1, 1, 2, 3, 2, 2]
def baseStart_4244462 : Nat := 118140960795 + 4244462 * 2 ^ 59
def prefixEnd_4244462 : Nat := 4983230072969 + 3 ^ 40 * 4244462 * 2
def baseEnd_4244462 : Nat := 2179449125743877756605081

theorem tailTrace_4244462 : CollatzResearch.WordTrace tailWord_4244462 prefixEnd_4244462 2179449125743877756605081 := by
  unfold tailWord_4244462
  simp only [CollatzResearch.WordTrace]
  refine ⟨19351030893630818155344955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103205498099364363495173093 19351030893630818155344955)
  ·
    refine ⟨29026546340446227233017433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19351030893630818155344955 29026546340446227233017433)
    ·
      refine ⟨21769909755334670424763075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29026546340446227233017433 21769909755334670424763075)
      ·
        refine ⟨32654864633002005637144613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21769909755334670424763075 32654864633002005637144613)
        ·
          refine ⟨6122787118687876056964615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32654864633002005637144613 6122787118687876056964615)
          ·
            refine ⟨9184180678031814085446923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6122787118687876056964615 9184180678031814085446923)
            ·
              refine ⟨13776271017047721128170385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9184180678031814085446923 13776271017047721128170385)
              ·
                refine ⟨10332203262785790846127789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13776271017047721128170385 10332203262785790846127789)
                ·
                  refine ⟨3874576223544671567297921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10332203262785790846127789 3874576223544671567297921)
                  ·
                    refine ⟨2905932167658503675473441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3874576223544671567297921 2905932167658503675473441)
                    ·
                      refine ⟨2179449125743877756605081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2905932167658503675473441 2179449125743877756605081)
                      ·
                        rfl

theorem cell23_4244462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 3, 2, 2].length) (baseStart_4244462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4244462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4244462 prefixEnd_4244462 := by exact prefixLift 4244462
  have htrace : WordTrace (prefixWord ++ tailWord_4244462) baseStart_4244462 baseEnd_4244462 := by
    simpa [prefixWord, tailWord_4244462, baseEnd_4244462] using wordTrace_append hprefix tailTrace_4244462
  have hstable : (prefixWord ++ tailWord_4244462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4244462).length < 2 ^ (prefixWord ++ tailWord_4244462).sum := by decide
  have hdescent : baseEnd_4244462 < baseStart_4244462 := by decide
  rcases family_descends (prefixWord ++ tailWord_4244462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4244464 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 4, 7]
def baseStart_4244464 : Nat := 118140960795 + 4244464 * 2 ^ 59
def prefixEnd_4244464 : Nat := 4983230072969 + 3 ^ 40 * 4244464 * 2
def baseEnd_4244464 : Nat := 726483384235062249593357

theorem tailTrace_4244464 : CollatzResearch.WordTrace tailWord_4244464 prefixEnd_4244464 726483384235062249593357 := by
  unfold tailWord_4244464
  simp only [CollatzResearch.WordTrace]
  refine ⟨77404160047519649792166223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103205546730026199722888297 77404160047519649792166223)
  ·
    refine ⟨116106240071279474688249335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77404160047519649792166223 116106240071279474688249335)
    ·
      refine ⟨174159360106919212032374003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116106240071279474688249335 174159360106919212032374003)
      ·
        refine ⟨261239040160378818048561005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174159360106919212032374003 261239040160378818048561005)
        ·
          refine ⟨97964640060142056768210377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 261239040160378818048561005 97964640060142056768210377)
          ·
            refine ⟨73473480045106542576157783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97964640060142056768210377 73473480045106542576157783)
            ·
              refine ⟨110210220067659813864236675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73473480045106542576157783 110210220067659813864236675)
              ·
                refine ⟨165315330101489720796355013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110210220067659813864236675 165315330101489720796355013)
                ·
                  refine ⟨30996624394029322649316565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 165315330101489720796355013 30996624394029322649316565)
                  ·
                    refine ⟨726483384235062249593357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30996624394029322649316565 726483384235062249593357)
                    ·
                      rfl

theorem cell23_4244464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 4, 7].length) (baseStart_4244464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4244464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4244464 prefixEnd_4244464 := by exact prefixLift 4244464
  have htrace : WordTrace (prefixWord ++ tailWord_4244464) baseStart_4244464 baseEnd_4244464 := by
    simpa [prefixWord, tailWord_4244464, baseEnd_4244464] using wordTrace_append hprefix tailTrace_4244464
  have hstable : (prefixWord ++ tailWord_4244464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4244464).length < 2 ^ (prefixWord ++ tailWord_4244464).sum := by decide
  have hdescent : baseEnd_4244464 < baseStart_4244464 := by decide
  rcases family_descends (prefixWord ++ tailWord_4244464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4244511 : List Nat := [1, 1, 2, 4, 1, 3, 2, 1, 2, 6]
def baseStart_4244511 : Nat := 118140960795 + 4244511 * 2 ^ 59
def prefixEnd_4244511 : Nat := 4983230072969 + 3 ^ 40 * 4244511 * 2
def baseEnd_4244511 : Nat := 726491428765316021630785

theorem tailTrace_4244511 : CollatzResearch.WordTrace tailWord_4244511 prefixEnd_4244511 726491428765316021630785 := by
  unfold tailWord_4244511
  simp only [CollatzResearch.WordTrace]
  refine ⟨154810034325869026611293387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103206689550579351074195591 154810034325869026611293387)
  ·
    refine ⟨232215051488803539916940081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154810034325869026611293387 232215051488803539916940081)
    ·
      refine ⟨174161288616602654937705061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 232215051488803539916940081 174161288616602654937705061)
      ·
        refine ⟨32655241615612997800819699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 174161288616602654937705061 32655241615612997800819699)
        ·
          refine ⟨48982862423419496701229549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32655241615612997800819699 48982862423419496701229549)
          ·
            refine ⟨18368573408782311262961081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48982862423419496701229549 18368573408782311262961081)
            ·
              refine ⟨13776430056586733447220811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18368573408782311262961081 13776430056586733447220811)
              ·
                refine ⟨20664645084880100170831217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13776430056586733447220811 20664645084880100170831217)
                ·
                  refine ⟨15498483813660075128123413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20664645084880100170831217 15498483813660075128123413)
                  ·
                    refine ⟨726491428765316021630785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15498483813660075128123413 726491428765316021630785)
                    ·
                      rfl

theorem cell23_4244511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 6].length) (baseStart_4244511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4244511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4244511 prefixEnd_4244511 := by exact prefixLift 4244511
  have htrace : WordTrace (prefixWord ++ tailWord_4244511) baseStart_4244511 baseEnd_4244511 := by
    simpa [prefixWord, tailWord_4244511, baseEnd_4244511] using wordTrace_append hprefix tailTrace_4244511
  have hstable : (prefixWord ++ tailWord_4244511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4244511).length < 2 ^ (prefixWord ++ tailWord_4244511).sum := by decide
  have hdescent : baseEnd_4244511 < baseStart_4244511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4244511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4244512 : List Nat := [2, 1, 1, 7, 1, 2, 1, 1, 1, 3, 3]
def baseStart_4244512 : Nat := 118140960795 + 4244512 * 2 ^ 59
def prefixEnd_4244512 : Nat := 4983230072969 + 3 ^ 40 * 4244512 * 2
def baseEnd_4244512 : Nat := 2179474799776602560979851

theorem tailTrace_4244512 : CollatzResearch.WordTrace tailWord_4244512 prefixEnd_4244512 2179474799776602560979851 := by
  unfold tailWord_4244512
  simp only [CollatzResearch.WordTrace]
  refine ⟨77405035399432701891039895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103206713865910269188053193 77405035399432701891039895)
  ·
    refine ⟨116107553099149052836559843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77405035399432701891039895 116107553099149052836559843)
    ·
      refine ⟨174161329648723579254839765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116107553099149052836559843 174161329648723579254839765)
      ·
        refine ⟨4081906163641958888785307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 174161329648723579254839765 4081906163641958888785307)
        ·
          refine ⟨6122859245462938333177961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4081906163641958888785307 6122859245462938333177961)
          ·
            refine ⟨4592144434097203749883471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6122859245462938333177961 4592144434097203749883471)
            ·
              refine ⟨6888216651145805624825207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4592144434097203749883471 6888216651145805624825207)
              ·
                refine ⟨10332324976718708437237811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6888216651145805624825207 10332324976718708437237811)
                ·
                  refine ⟨15498487465078062655856717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10332324976718708437237811 15498487465078062655856717)
                  ·
                    refine ⟨5811932799404273495946269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15498487465078062655856717 5811932799404273495946269)
                    ·
                      refine ⟨2179474799776602560979851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5811932799404273495946269 2179474799776602560979851)
                      ·
                        rfl

theorem cell23_4244512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_4244512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4244512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4244512 prefixEnd_4244512 := by exact prefixLift 4244512
  have htrace : WordTrace (prefixWord ++ tailWord_4244512) baseStart_4244512 baseEnd_4244512 := by
    simpa [prefixWord, tailWord_4244512, baseEnd_4244512] using wordTrace_append hprefix tailTrace_4244512
  have hstable : (prefixWord ++ tailWord_4244512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4244512).length < 2 ^ (prefixWord ++ tailWord_4244512).sum := by decide
  have hdescent : baseEnd_4244512 < baseStart_4244512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4244512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4244581 : List Nat := [1, 3, 1, 3, 2, 1, 1, 2, 1, 1, 7]
def baseStart_4244581 : Nat := 118140960795 + 4244581 * 2 ^ 59
def prefixEnd_4244581 : Nat := 4983230072969 + 3 ^ 40 * 4244581 * 2
def baseEnd_4244581 : Nat := 2179510229941762791017033

theorem tailTrace_4244581 : CollatzResearch.WordTrace tailWord_4244581 prefixEnd_4244581 2179510229941762791017033 := by
  unfold tailWord_4244581
  simp only [CollatzResearch.WordTrace]
  refine ⟨154812587435615428566341597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103208391623743619044227731 154812587435615428566341597)
  ·
    refine ⟨58054720288355785712378099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154812587435615428566341597 58054720288355785712378099)
    ·
      refine ⟨87082080432533678568567149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58054720288355785712378099 87082080432533678568567149)
      ·
        refine ⟨32655780162200129463212681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87082080432533678568567149 32655780162200129463212681)
        ·
          refine ⟨24491835121650097097409511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32655780162200129463212681 24491835121650097097409511)
          ·
            refine ⟨36737752682475145646114267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24491835121650097097409511 36737752682475145646114267)
            ·
              refine ⟨55106629023712718469171401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36737752682475145646114267 55106629023712718469171401)
              ·
                refine ⟨41329971767784538851878551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55106629023712718469171401 41329971767784538851878551)
                ·
                  refine ⟨61994957651676808277817827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41329971767784538851878551 61994957651676808277817827)
                  ·
                    refine ⟨92992436477515212416726741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61994957651676808277817827 92992436477515212416726741)
                    ·
                      refine ⟨2179510229941762791017033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 92992436477515212416726741 2179510229941762791017033)
                      ·
                        rfl

theorem cell23_4244581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_4244581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4244581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4244581 prefixEnd_4244581 := by exact prefixLift 4244581
  have htrace : WordTrace (prefixWord ++ tailWord_4244581) baseStart_4244581 baseEnd_4244581 := by
    simpa [prefixWord, tailWord_4244581, baseEnd_4244581] using wordTrace_append hprefix tailTrace_4244581
  have hstable : (prefixWord ++ tailWord_4244581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4244581).length < 2 ^ (prefixWord ++ tailWord_4244581).sum := by decide
  have hdescent : baseEnd_4244581 < baseStart_4244581 := by decide
  rcases family_descends (prefixWord ++ tailWord_4244581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4244588 : List Nat := [2, 2, 1, 1, 3, 2, 4, 1, 2, 5]
def baseStart_4244588 : Nat := 118140960795 + 4244588 * 2 ^ 59
def prefixEnd_4244588 : Nat := 4983230072969 + 3 ^ 40 * 4244588 * 2
def baseEnd_4244588 : Nat := 726504608102114754543167

theorem tailTrace_4244588 : CollatzResearch.WordTrace tailWord_4244588 prefixEnd_4244588 726504608102114754543167 := by
  unfold tailWord_4244588
  simp only [CollatzResearch.WordTrace]
  refine ⟨77406421373295034380923209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103208561831060045841230945 77406421373295034380923209)
  ·
    refine ⟨58054816029971275785692407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77406421373295034380923209 58054816029971275785692407)
    ·
      refine ⟨87082224044956913678538611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58054816029971275785692407 87082224044956913678538611)
      ·
        refine ⟨130623336067435370517807917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87082224044956913678538611 130623336067435370517807917)
        ·
          refine ⟨48983751025288263944177969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130623336067435370517807917 48983751025288263944177969)
          ·
            refine ⟨36737813268966197958133477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48983751025288263944177969 36737813268966197958133477)
            ·
              refine ⟨6888339987931162117150027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36737813268966197958133477 6888339987931162117150027)
              ·
                refine ⟨10332509981896743175725041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6888339987931162117150027 10332509981896743175725041)
                ·
                  refine ⟨7749382486422557381793781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10332509981896743175725041 7749382486422557381793781)
                  ·
                    refine ⟨726504608102114754543167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7749382486422557381793781 726504608102114754543167)
                    ·
                      rfl

theorem cell23_4244588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 5].length) (baseStart_4244588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4244588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4244588 prefixEnd_4244588 := by exact prefixLift 4244588
  have htrace : WordTrace (prefixWord ++ tailWord_4244588) baseStart_4244588 baseEnd_4244588 := by
    simpa [prefixWord, tailWord_4244588, baseEnd_4244588] using wordTrace_append hprefix tailTrace_4244588
  have hstable : (prefixWord ++ tailWord_4244588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4244588).length < 2 ^ (prefixWord ++ tailWord_4244588).sum := by decide
  have hdescent : baseEnd_4244588 < baseStart_4244588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4244588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4244598 : List Nat := [5, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5]
def baseStart_4244598 : Nat := 118140960795 + 4244598 * 2 ^ 59
def prefixEnd_4244598 : Nat := 4983230072969 + 3 ^ 40 * 4244598 * 2
def baseEnd_4244598 : Nat := 2179518959112889224504455

theorem tailTrace_4244598 : CollatzResearch.WordTrace tailWord_4244598 prefixEnd_4244598 2179518959112889224504455 := by
  unfold tailWord_4244598
  simp only [CollatzResearch.WordTrace]
  refine ⟨9675825467284615029356903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 103208804984369226979806965 9675825467284615029356903)
  ·
    refine ⟨14513738200926922544035355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9675825467284615029356903 14513738200926922544035355)
    ·
      refine ⟨21770607301390383816053033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14513738200926922544035355 21770607301390383816053033)
      ·
        refine ⟨16327955476042787862039775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21770607301390383816053033 16327955476042787862039775)
        ·
          refine ⟨24491933214064181793059663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16327955476042787862039775 24491933214064181793059663)
          ·
            refine ⟨36737899821096272689589495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24491933214064181793059663 36737899821096272689589495)
            ·
              refine ⟨55106849731644409034384243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36737899821096272689589495 55106849731644409034384243)
              ·
                refine ⟨82660274597466613551576365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55106849731644409034384243 82660274597466613551576365)
                ·
                  refine ⟨30997602974049980081841137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82660274597466613551576365 30997602974049980081841137)
                  ·
                    refine ⟨23248202230537485061380853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30997602974049980081841137 23248202230537485061380853)
                    ·
                      refine ⟨2179518959112889224504455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23248202230537485061380853 2179518959112889224504455)
                      ·
                        rfl

theorem cell23_4244598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_4244598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4244598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4244598 prefixEnd_4244598 := by exact prefixLift 4244598
  have htrace : WordTrace (prefixWord ++ tailWord_4244598) baseStart_4244598 baseEnd_4244598 := by
    simpa [prefixWord, tailWord_4244598, baseEnd_4244598] using wordTrace_append hprefix tailTrace_4244598
  have hstable : (prefixWord ++ tailWord_4244598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4244598).length < 2 ^ (prefixWord ++ tailWord_4244598).sum := by decide
  have hdescent : baseEnd_4244598 < baseStart_4244598 := by decide
  rcases family_descends (prefixWord ++ tailWord_4244598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4244608 : List Nat := [2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 4]
def baseStart_4244608 : Nat := 118140960795 + 4244608 * 2 ^ 59
def prefixEnd_4244608 : Nat := 4983230072969 + 3 ^ 40 * 4244608 * 2
def baseEnd_4244608 : Nat := 2179524093919434185379409

theorem tailTrace_4244608 : CollatzResearch.WordTrace tailWord_4244608 prefixEnd_4244608 2179524093919434185379409 := by
  unfold tailWord_4244608
  simp only [CollatzResearch.WordTrace]
  refine ⟨77406786103258806088787239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103209048137678408118382985 77406786103258806088787239)
  ·
    refine ⟨116110179154888209133180859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77406786103258806088787239 116110179154888209133180859)
    ·
      refine ⟨174165268732332313699771289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116110179154888209133180859 174165268732332313699771289)
      ·
        refine ⟨130623951549249235274828467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174165268732332313699771289 130623951549249235274828467)
        ·
          refine ⟨195935927323873852912242701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130623951549249235274828467 195935927323873852912242701)
          ·
            refine ⟨73475972746452694842091013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 195935927323873852912242701 73475972746452694842091013)
            ·
              refine ⟨13776744889959880282892065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73475972746452694842091013 13776744889959880282892065)
              ·
                refine ⟨10332558667469910212169049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13776744889959880282892065 10332558667469910212169049)
                ·
                  refine ⟨7749419000602432659126787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10332558667469910212169049 7749419000602432659126787)
                  ·
                    refine ⟨11624128500903648988690181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7749419000602432659126787 11624128500903648988690181)
                    ·
                      refine ⟨2179524093919434185379409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11624128500903648988690181 2179524093919434185379409)
                      ·
                        rfl

theorem cell23_4244608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 4].length) (baseStart_4244608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4244608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4244608 prefixEnd_4244608 := by exact prefixLift 4244608
  have htrace : WordTrace (prefixWord ++ tailWord_4244608) baseStart_4244608 baseEnd_4244608 := by
    simpa [prefixWord, tailWord_4244608, baseEnd_4244608] using wordTrace_append hprefix tailTrace_4244608
  have hstable : (prefixWord ++ tailWord_4244608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4244608).length < 2 ^ (prefixWord ++ tailWord_4244608).sum := by decide
  have hdescent : baseEnd_4244608 < baseStart_4244608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4244608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4244611 : List Nat := [1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 5]
def baseStart_4244611 : Nat := 118140960795 + 4244611 * 2 ^ 59
def prefixEnd_4244611 : Nat := 4983230072969 + 3 ^ 40 * 4244611 * 2
def baseEnd_4244611 : Nat := 2179525634361397673641895

theorem tailTrace_4244611 : CollatzResearch.WordTrace tailWord_4244611 prefixEnd_4244611 2179525634361397673641895 := by
  unfold tailWord_4244611
  simp only [CollatzResearch.WordTrace]
  refine ⟨154813681625506743689933687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103209121083671162459955791 154813681625506743689933687)
  ·
    refine ⟨232220522438260115534900531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154813681625506743689933687 232220522438260115534900531)
    ·
      refine ⟨348330783657390173302350797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232220522438260115534900531 348330783657390173302350797)
      ·
        refine ⟨130624043871521314988381549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 348330783657390173302350797 130624043871521314988381549)
        ·
          refine ⟨48984016451820493120643081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130624043871521314988381549 48984016451820493120643081)
          ·
            refine ⟨36738012338865369840482311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48984016451820493120643081 36738012338865369840482311)
            ·
              refine ⟨55107018508298054760723467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36738012338865369840482311 55107018508298054760723467)
              ·
                refine ⟨82660527762447082141085201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55107018508298054760723467 82660527762447082141085201)
                ·
                  refine ⟨61995395821835311605813901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82660527762447082141085201 61995395821835311605813901)
                  ·
                    refine ⟨23248273433188241852180213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61995395821835311605813901 23248273433188241852180213)
                    ·
                      refine ⟨2179525634361397673641895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23248273433188241852180213 2179525634361397673641895)
                      ·
                        rfl

theorem cell23_4244611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 5].length) (baseStart_4244611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4244611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4244611 prefixEnd_4244611 := by exact prefixLift 4244611
  have htrace : WordTrace (prefixWord ++ tailWord_4244611) baseStart_4244611 baseEnd_4244611 := by
    simpa [prefixWord, tailWord_4244611, baseEnd_4244611] using wordTrace_append hprefix tailTrace_4244611
  have hstable : (prefixWord ++ tailWord_4244611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4244611).length < 2 ^ (prefixWord ++ tailWord_4244611).sum := by decide
  have hdescent : baseEnd_4244611 < baseStart_4244611 := by decide
  rcases family_descends (prefixWord ++ tailWord_4244611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4244645 : List Nat := [1, 3, 1, 2, 1, 4, 3, 1, 2, 2, 3]
def baseStart_4244645 : Nat := 118140960795 + 4244645 * 2 ^ 59
def prefixEnd_4244645 : Nat := 4983230072969 + 3 ^ 40 * 4244645 * 2
def baseEnd_4244645 : Nat := 2179543092703650540616739

theorem tailTrace_4244645 : CollatzResearch.WordTrace tailWord_4244645 prefixEnd_4244645 2179543092703650540616739 := by
  unfold tailWord_4244645
  simp only [CollatzResearch.WordTrace]
  refine ⟨154814921707383567496671389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103209947804922378331114259 154814921707383567496671389)
  ·
    refine ⟨58055595640268837811251771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154814921707383567496671389 58055595640268837811251771)
    ·
      refine ⟨87083393460403256716877657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58055595640268837811251771 87083393460403256716877657)
      ·
        refine ⟨65312545095302442537658243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87083393460403256716877657 65312545095302442537658243)
        ·
          refine ⟨97968817642953663806487365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65312545095302442537658243 97968817642953663806487365)
          ·
            refine ⟨18369153308053811963716381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 97968817642953663806487365 18369153308053811963716381)
            ·
              refine ⟨6888432490520179486393643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18369153308053811963716381 6888432490520179486393643)
              ·
                refine ⟨10332648735780269229590465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6888432490520179486393643 10332648735780269229590465)
                ·
                  refine ⟨7749486551835201922192849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10332648735780269229590465 7749486551835201922192849)
                  ·
                    refine ⟨5812114913876401441644637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7749486551835201922192849 5812114913876401441644637)
                    ·
                      refine ⟨2179543092703650540616739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5812114913876401441644637 2179543092703650540616739)
                      ·
                        rfl

theorem cell23_4244645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 2, 2, 3].length) (baseStart_4244645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4244645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4244645 prefixEnd_4244645 := by exact prefixLift 4244645
  have htrace : WordTrace (prefixWord ++ tailWord_4244645) baseStart_4244645 baseEnd_4244645 := by
    simpa [prefixWord, tailWord_4244645, baseEnd_4244645] using wordTrace_append hprefix tailTrace_4244645
  have hstable : (prefixWord ++ tailWord_4244645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4244645).length < 2 ^ (prefixWord ++ tailWord_4244645).sum := by decide
  have hdescent : baseEnd_4244645 < baseStart_4244645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4244645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4244665 : List Nat := [1, 2, 1, 4, 1, 5, 1, 2, 6]
def baseStart_4244665 : Nat := 118140960795 + 4244665 * 2 ^ 59
def prefixEnd_4244665 : Nat := 4983230072969 + 3 ^ 40 * 4244665 * 2
def baseEnd_4244665 : Nat := 242172595812971162485183

theorem tailTrace_4244665 : CollatzResearch.WordTrace tailWord_4244665 prefixEnd_4244665 242172595812971162485183 := by
  unfold tailWord_4244665
  simp only [CollatzResearch.WordTrace]
  refine ⟨154815651167311110912399449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103210434111540740608266299 154815651167311110912399449)
  ·
    refine ⟨116111738375483333184299587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154815651167311110912399449 116111738375483333184299587)
    ·
      refine ⟨174167607563224999776449381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116111738375483333184299587 174167607563224999776449381)
      ·
        refine ⟨32656426418104687458084259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 174167607563224999776449381 32656426418104687458084259)
        ·
          refine ⟨48984639627157031187126389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32656426418104687458084259 48984639627157031187126389)
          ·
            refine ⟨4592309965045971673793099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48984639627157031187126389 4592309965045971673793099)
            ·
              refine ⟨6888464947568957510689649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4592309965045971673793099 6888464947568957510689649)
              ·
                refine ⟨5166348710676718133017237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6888464947568957510689649 5166348710676718133017237)
                ·
                  refine ⟨242172595812971162485183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5166348710676718133017237 242172595812971162485183)
                  ·
                    rfl

theorem cell23_4244665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 2, 6].length) (baseStart_4244665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4244665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4244665 prefixEnd_4244665 := by exact prefixLift 4244665
  have htrace : WordTrace (prefixWord ++ tailWord_4244665) baseStart_4244665 baseEnd_4244665 := by
    simpa [prefixWord, tailWord_4244665, baseEnd_4244665] using wordTrace_append hprefix tailTrace_4244665
  have hstable : (prefixWord ++ tailWord_4244665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4244665).length < 2 ^ (prefixWord ++ tailWord_4244665).sum := by decide
  have hdescent : baseEnd_4244665 < baseStart_4244665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4244665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4244668 : List Nat := [2, 2, 2, 3, 2, 1, 1, 1, 1, 2, 6]
def baseStart_4244668 : Nat := 118140960795 + 4244668 * 2 ^ 59
def prefixEnd_4244668 : Nat := 4983230072969 + 3 ^ 40 * 4244668 * 2
def baseEnd_4244668 : Nat := 2179554902758703950629133

theorem tailTrace_4244668 : CollatzResearch.WordTrace tailWord_4244668 prefixEnd_4244668 2179554902758703950629133 := by
  unfold tailWord_4244668
  simp only [CollatzResearch.WordTrace]
  refine ⟨77407880293150121212379329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103210507057533494949839105 77407880293150121212379329)
  ·
    refine ⟨58055910219862590909284497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77407880293150121212379329 58055910219862590909284497)
    ·
      refine ⟨43541932664896943181963373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58055910219862590909284497 43541932664896943181963373)
      ·
        refine ⟨16328224749336353693236265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43541932664896943181963373 16328224749336353693236265)
        ·
          refine ⟨12246168562002265269927199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16328224749336353693236265 12246168562002265269927199)
          ·
            refine ⟨18369252843003397904890799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12246168562002265269927199 18369252843003397904890799)
            ·
              refine ⟨27553879264505096857336199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18369252843003397904890799 27553879264505096857336199)
              ·
                refine ⟨41330818896757645286004299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27553879264505096857336199 41330818896757645286004299)
                ·
                  refine ⟨61996228345136467929006449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41330818896757645286004299 61996228345136467929006449)
                  ·
                    refine ⟨46497171258852350946754837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61996228345136467929006449 46497171258852350946754837)
                    ·
                      refine ⟨2179554902758703950629133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46497171258852350946754837 2179554902758703950629133)
                      ·
                        rfl

theorem cell23_4244668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_4244668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4244668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4244668 prefixEnd_4244668 := by exact prefixLift 4244668
  have htrace : WordTrace (prefixWord ++ tailWord_4244668) baseStart_4244668 baseEnd_4244668 := by
    simpa [prefixWord, tailWord_4244668, baseEnd_4244668] using wordTrace_append hprefix tailTrace_4244668
  have hstable : (prefixWord ++ tailWord_4244668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4244668).length < 2 ^ (prefixWord ++ tailWord_4244668).sum := by decide
  have hdescent : baseEnd_4244668 < baseStart_4244668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4244668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4244708 : List Nat := [2, 3, 1, 1, 1, 2, 2, 4, 1, 6]
def baseStart_4244708 : Nat := 118140960795 + 4244708 * 2 ^ 59
def prefixEnd_4244708 : Nat := 4983230072969 + 3 ^ 40 * 4244708 * 2
def baseEnd_4244708 : Nat := 726525147328294598042983

theorem tailTrace_4244708 : CollatzResearch.WordTrace tailWord_4244708 prefixEnd_4244708 726525147328294598042983 := by
  unfold tailWord_4244708
  simp only [CollatzResearch.WordTrace]
  refine ⟨77408609753077664628107389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103211479670770219504143185 77408609753077664628107389)
  ·
    refine ⟨29028228657404124235540271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77408609753077664628107389 29028228657404124235540271)
    ·
      refine ⟨43542342986106186353310407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29028228657404124235540271 43542342986106186353310407)
      ·
        refine ⟨65313514479159279529965611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43542342986106186353310407 65313514479159279529965611)
        ·
          refine ⟨97970271718738919294948417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65313514479159279529965611 97970271718738919294948417)
          ·
            refine ⟨73477703789054189471211313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97970271718738919294948417 73477703789054189471211313)
            ·
              refine ⟨55108277841790642103408485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73477703789054189471211313 55108277841790642103408485)
              ·
                refine ⟨10332802095335745394389091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55108277841790642103408485 10332802095335745394389091)
                ·
                  refine ⟨15499203143003618091583637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10332802095335745394389091 15499203143003618091583637)
                  ·
                    refine ⟨726525147328294598042983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15499203143003618091583637 726525147328294598042983)
                    ·
                      rfl

theorem cell23_4244708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 1, 6].length) (baseStart_4244708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4244708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4244708 prefixEnd_4244708 := by exact prefixLift 4244708
  have htrace : WordTrace (prefixWord ++ tailWord_4244708) baseStart_4244708 baseEnd_4244708 := by
    simpa [prefixWord, tailWord_4244708, baseEnd_4244708] using wordTrace_append hprefix tailTrace_4244708
  have hstable : (prefixWord ++ tailWord_4244708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4244708).length < 2 ^ (prefixWord ++ tailWord_4244708).sum := by decide
  have hdescent : baseEnd_4244708 < baseStart_4244708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4244708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4244715 : List Nat := [1, 1, 1, 1, 2, 6, 2, 3, 1, 1, 4]
def baseStart_4244715 : Nat := 118140960795 + 4244715 * 2 ^ 59
def prefixEnd_4244715 : Nat := 4983230072969 + 3 ^ 40 * 4244715 * 2
def baseEnd_4244715 : Nat := 2179579036349465266741417

theorem tailTrace_4244715 : CollatzResearch.WordTrace tailWord_4244715 prefixEnd_4244715 2179579036349465266741417 := by
  unfold tailWord_4244715
  simp only [CollatzResearch.WordTrace]
  refine ⟨154817474817129969451719599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103211649878086646301146399 154817474817129969451719599)
  ·
    refine ⟨232226212225694954177579399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154817474817129969451719599 232226212225694954177579399)
    ·
      refine ⟨348339318338542431266369099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232226212225694954177579399 348339318338542431266369099)
      ·
        refine ⟨522508977507813646899553649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 348339318338542431266369099 522508977507813646899553649)
        ·
          refine ⟨391881733130860235174665237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 522508977507813646899553649 391881733130860235174665237)
          ·
            refine ⟨18369456240509073523812433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 391881733130860235174665237 18369456240509073523812433)
            ·
              refine ⟨13777092180381805142859325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18369456240509073523812433 13777092180381805142859325)
              ·
                refine ⟨5166409567643176928572247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13777092180381805142859325 5166409567643176928572247)
                ·
                  refine ⟨7749614351464765392858371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5166409567643176928572247 7749614351464765392858371)
                  ·
                    refine ⟨11624421527197148089287557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7749614351464765392858371 11624421527197148089287557)
                    ·
                      refine ⟨2179579036349465266741417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11624421527197148089287557 2179579036349465266741417)
                      ·
                        rfl

theorem cell23_4244715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 3, 1, 1, 4].length) (baseStart_4244715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4244715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4244715 prefixEnd_4244715 := by exact prefixLift 4244715
  have htrace : WordTrace (prefixWord ++ tailWord_4244715) baseStart_4244715 baseEnd_4244715 := by
    simpa [prefixWord, tailWord_4244715, baseEnd_4244715] using wordTrace_append hprefix tailTrace_4244715
  have hstable : (prefixWord ++ tailWord_4244715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4244715).length < 2 ^ (prefixWord ++ tailWord_4244715).sum := by decide
  have hdescent : baseEnd_4244715 < baseStart_4244715 := by decide
  rcases family_descends (prefixWord ++ tailWord_4244715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4244806 : List Nat := [6, 1, 1, 3, 1, 1, 3, 7]
def baseStart_4244806 : Nat := 118140960795 + 4244806 * 2 ^ 59
def prefixEnd_4244806 : Nat := 4983230072969 + 3 ^ 40 * 4244806 * 2
def baseEnd_4244806 : Nat := 80726880114408311507537

theorem tailTrace_4244806 : CollatzResearch.WordTrace tailWord_4244806 prefixEnd_4244806 80726880114408311507537 := by
  unfold tailWord_4244806
  simp only [CollatzResearch.WordTrace]
  refine ⟨4838149808118759124790071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 103213862573200194662188181 4838149808118759124790071)
  ·
    refine ⟨7257224712178138687185107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4838149808118759124790071 7257224712178138687185107)
    ·
      refine ⟨10885837068267208030777661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7257224712178138687185107 10885837068267208030777661)
      ·
        refine ⟨4082188900600203011541623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10885837068267208030777661 4082188900600203011541623)
        ·
          refine ⟨6123283350900304517312435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4082188900600203011541623 6123283350900304517312435)
          ·
            refine ⟨9184925026350456775968653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6123283350900304517312435 9184925026350456775968653)
            ·
              refine ⟨3444346884881421290988245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9184925026350456775968653 3444346884881421290988245)
              ·
                refine ⟨80726880114408311507537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3444346884881421290988245 80726880114408311507537)
                ·
                  rfl

theorem cell23_4244806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 7].length) (baseStart_4244806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4244806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4244806 prefixEnd_4244806 := by exact prefixLift 4244806
  have htrace : WordTrace (prefixWord ++ tailWord_4244806) baseStart_4244806 baseEnd_4244806 := by
    simpa [prefixWord, tailWord_4244806, baseEnd_4244806] using wordTrace_append hprefix tailTrace_4244806
  have hstable : (prefixWord ++ tailWord_4244806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4244806).length < 2 ^ (prefixWord ++ tailWord_4244806).sum := by decide
  have hdescent : baseEnd_4244806 < baseStart_4244806 := by decide
  rcases family_descends (prefixWord ++ tailWord_4244806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4244835 : List Nat := [1, 1, 1, 5, 2, 2, 1, 2, 2, 2, 4]
def baseStart_4244835 : Nat := 118140960795 + 4244835 * 2 ^ 59
def prefixEnd_4244835 : Nat := 4983230072969 + 3 ^ 40 * 4244835 * 2
def baseEnd_4244835 : Nat := 2179640654028004797240865

theorem tailTrace_4244835 : CollatzResearch.WordTrace tailWord_4244835 prefixEnd_4244835 2179640654028004797240865 := by
  unfold tailWord_4244835
  simp only [CollatzResearch.WordTrace]
  refine ⟨154821851576695229946087959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103214567717796819964058639 154821851576695229946087959)
  ·
    refine ⟨232232777365042844919131939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154821851576695229946087959 232232777365042844919131939)
    ·
      refine ⟨348349166047564267378697909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232232777365042844919131939 348349166047564267378697909)
      ·
        refine ⟨32657734316959150066752929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 348349166047564267378697909 32657734316959150066752929)
        ·
          refine ⟨24493300737719362550064697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32657734316959150066752929 24493300737719362550064697)
          ·
            refine ⟨18369975553289521912548523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24493300737719362550064697 18369975553289521912548523)
            ·
              refine ⟨27554963329934282868822785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18369975553289521912548523 27554963329934282868822785)
              ·
                refine ⟨20666222497450712151617089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27554963329934282868822785 20666222497450712151617089)
                ·
                  refine ⟨15499666873088034113712817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20666222497450712151617089 15499666873088034113712817)
                  ·
                    refine ⟨11624750154816025585284613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15499666873088034113712817 11624750154816025585284613)
                    ·
                      refine ⟨2179640654028004797240865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11624750154816025585284613 2179640654028004797240865)
                      ·
                        rfl

theorem cell23_4244835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_4244835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4244835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4244835 prefixEnd_4244835 := by exact prefixLift 4244835
  have htrace : WordTrace (prefixWord ++ tailWord_4244835) baseStart_4244835 baseEnd_4244835 := by
    simpa [prefixWord, tailWord_4244835, baseEnd_4244835] using wordTrace_append hprefix tailTrace_4244835
  have hstable : (prefixWord ++ tailWord_4244835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4244835).length < 2 ^ (prefixWord ++ tailWord_4244835).sum := by decide
  have hdescent : baseEnd_4244835 < baseStart_4244835 := by decide
  rcases family_descends (prefixWord ++ tailWord_4244835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4244845 : List Nat := [1, 5, 1, 1, 1, 3, 1, 3, 7]
def baseStart_4244845 : Nat := 118140960795 + 4244845 * 2 ^ 59
def prefixEnd_4244845 : Nat := 4983230072969 + 3 ^ 40 * 4244845 * 2
def baseEnd_4244845 : Nat := 242182865426061084235091

theorem tailTrace_4244845 : CollatzResearch.WordTrace tailWord_4244845 prefixEnd_4244845 242182865426061084235091 := by
  unfold tailWord_4244845
  simp only [CollatzResearch.WordTrace]
  refine ⟨154822216306659001653951989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103214810871106001102634659 154822216306659001653951989)
  ·
    refine ⟨14514582778749281405057999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 154822216306659001653951989 14514582778749281405057999)
    ·
      refine ⟨21771874168123922107586999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14514582778749281405057999 21771874168123922107586999)
      ·
        refine ⟨32657811252185883161380499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21771874168123922107586999 32657811252185883161380499)
        ·
          refine ⟨48986716878278824742070749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32657811252185883161380499 48986716878278824742070749)
          ·
            refine ⟨18370018829354559278276531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48986716878278824742070749 18370018829354559278276531)
            ·
              refine ⟨27555028244031838917414797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18370018829354559278276531 27555028244031838917414797)
              ·
                refine ⟨10333135591511939594030549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27555028244031838917414797 10333135591511939594030549)
                ·
                  refine ⟨242182865426061084235091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10333135591511939594030549 242182865426061084235091)
                  ·
                    rfl

theorem cell23_4244845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 7].length) (baseStart_4244845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4244845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4244845 prefixEnd_4244845 := by exact prefixLift 4244845
  have htrace : WordTrace (prefixWord ++ tailWord_4244845) baseStart_4244845 baseEnd_4244845 := by
    simpa [prefixWord, tailWord_4244845, baseEnd_4244845] using wordTrace_append hprefix tailTrace_4244845
  have hstable : (prefixWord ++ tailWord_4244845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4244845).length < 2 ^ (prefixWord ++ tailWord_4244845).sum := by decide
  have hdescent : baseEnd_4244845 < baseStart_4244845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4244845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4244855 : List Nat := [1, 1, 3, 1, 1, 2, 3, 3, 2, 3, 3]
def baseStart_4244855 : Nat := 118140960795 + 4244855 * 2 ^ 59
def prefixEnd_4244855 : Nat := 4983230072969 + 3 ^ 40 * 4244855 * 2
def baseEnd_4244855 : Nat := 2179650923641094718990773

theorem tailTrace_4244855 : CollatzResearch.WordTrace tailWord_4244855 prefixEnd_4244855 2179650923641094718990773 := by
  unfold tailWord_4244855
  simp only [CollatzResearch.WordTrace]
  refine ⟨154822581036622773361816019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103215054024415182241210679 154822581036622773361816019)
  ·
    refine ⟨232233871554934160042724029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154822581036622773361816019 232233871554934160042724029)
    ·
      refine ⟨87087701833100310016021511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 232233871554934160042724029 87087701833100310016021511)
      ·
        refine ⟨130631552749650465024032267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87087701833100310016021511 130631552749650465024032267)
        ·
          refine ⟨195947329124475697536048401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130631552749650465024032267 195947329124475697536048401)
          ·
            refine ⟨146960496843356773152036301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 195947329124475697536048401 146960496843356773152036301)
            ·
              refine ⟨55110186316258789932013613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 146960496843356773152036301 55110186316258789932013613)
              ·
                refine ⟨20666319868597046224505105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55110186316258789932013613 20666319868597046224505105)
                ·
                  refine ⟨15499739901447784668378829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20666319868597046224505105 15499739901447784668378829)
                  ·
                    refine ⟨5812402463042919250642061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15499739901447784668378829 5812402463042919250642061)
                    ·
                      refine ⟨2179650923641094718990773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5812402463042919250642061 2179650923641094718990773)
                      ·
                        rfl

theorem cell23_4244855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 3, 3].length) (baseStart_4244855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4244855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4244855 prefixEnd_4244855 := by exact prefixLift 4244855
  have htrace : WordTrace (prefixWord ++ tailWord_4244855) baseStart_4244855 baseEnd_4244855 := by
    simpa [prefixWord, tailWord_4244855, baseEnd_4244855] using wordTrace_append hprefix tailTrace_4244855
  have hstable : (prefixWord ++ tailWord_4244855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4244855).length < 2 ^ (prefixWord ++ tailWord_4244855).sum := by decide
  have hdescent : baseEnd_4244855 < baseStart_4244855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4244855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4244875 : List Nat := [1, 1, 1, 1, 4, 3, 2, 3, 2, 5]
def baseStart_4244875 : Nat := 118140960795 + 4244875 * 2 ^ 59
def prefixEnd_4244875 : Nat := 4983230072969 + 3 ^ 40 * 4244875 * 2
def baseEnd_4244875 : Nat := 726553731084728213580227

theorem tailTrace_4244875 : CollatzResearch.WordTrace tailWord_4244875 prefixEnd_4244875 726553731084728213580227 := by
  unfold tailWord_4244875
  simp only [CollatzResearch.WordTrace]
  refine ⟨154823310496550316777544079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103215540331033544518362719 154823310496550316777544079)
  ·
    refine ⟨232234965744825475166316119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154823310496550316777544079 232234965744825475166316119)
    ·
      refine ⟨348352448617238212749474179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232234965744825475166316119 348352448617238212749474179)
      ·
        refine ⟨522528672925857319124211269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 348352448617238212749474179 522528672925857319124211269)
        ·
          refine ⟨97974126173598247335789613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 522528672925857319124211269 97974126173598247335789613)
          ·
            refine ⟨36740297315099342750921105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97974126173598247335789613 36740297315099342750921105)
            ·
              refine ⟨27555222986324507063190829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36740297315099342750921105 27555222986324507063190829)
              ·
                refine ⟨10333208619871690148696561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27555222986324507063190829 10333208619871690148696561)
                ·
                  refine ⟨7749906464903767611522421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10333208619871690148696561 7749906464903767611522421)
                  ·
                    refine ⟨726553731084728213580227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7749906464903767611522421 726553731084728213580227)
                    ·
                      rfl

theorem cell23_4244875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 2, 5].length) (baseStart_4244875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4244875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4244875 prefixEnd_4244875 := by exact prefixLift 4244875
  have htrace : WordTrace (prefixWord ++ tailWord_4244875) baseStart_4244875 baseEnd_4244875 := by
    simpa [prefixWord, tailWord_4244875, baseEnd_4244875] using wordTrace_append hprefix tailTrace_4244875
  have hstable : (prefixWord ++ tailWord_4244875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4244875).length < 2 ^ (prefixWord ++ tailWord_4244875).sum := by decide
  have hdescent : baseEnd_4244875 < baseStart_4244875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4244875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4244915 : List Nat := [1, 1, 1, 2, 3, 1, 1, 3, 3, 4, 3]
def baseStart_4244915 : Nat := 118140960795 + 4244915 * 2 ^ 59
def prefixEnd_4244915 : Nat := 4983230072969 + 3 ^ 40 * 4244915 * 2
def baseEnd_4244915 : Nat := 2179681732480364484240497

theorem tailTrace_4244915 : CollatzResearch.WordTrace tailWord_4244915 prefixEnd_4244915 2179681732480364484240497 := by
  unfold tailWord_4244915
  simp only [CollatzResearch.WordTrace]
  refine ⟨154824769416405403609000199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103216512944270269072666799 154824769416405403609000199)
  ·
    refine ⟨232237154124608105413500299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154824769416405403609000199 232237154124608105413500299)
    ·
      refine ⟨348355731186912158120250449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232237154124608105413500299 348355731186912158120250449)
      ·
        refine ⟨261266798390184118590187837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 348355731186912158120250449 261266798390184118590187837)
        ·
          refine ⟨97975049396319044471320439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 261266798390184118590187837 97975049396319044471320439)
          ·
            refine ⟨146962574094478566706980659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97975049396319044471320439 146962574094478566706980659)
            ·
              refine ⟨220443861141717850060470989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146962574094478566706980659 220443861141717850060470989)
              ·
                refine ⟨82666447928144193772676621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 220443861141717850060470989 82666447928144193772676621)
                ·
                  refine ⟨30999917973054072664753733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82666447928144193772676621 30999917973054072664753733)
                  ·
                    refine ⟨5812484619947638624641325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30999917973054072664753733 5812484619947638624641325)
                    ·
                      refine ⟨2179681732480364484240497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5812484619947638624641325 2179681732480364484240497)
                      ·
                        rfl

theorem cell23_4244915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 4, 3].length) (baseStart_4244915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4244915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4244915 prefixEnd_4244915 := by exact prefixLift 4244915
  have htrace : WordTrace (prefixWord ++ tailWord_4244915) baseStart_4244915 baseEnd_4244915 := by
    simpa [prefixWord, tailWord_4244915, baseEnd_4244915] using wordTrace_append hprefix tailTrace_4244915
  have hstable : (prefixWord ++ tailWord_4244915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4244915).length < 2 ^ (prefixWord ++ tailWord_4244915).sum := by decide
  have hdescent : baseEnd_4244915 < baseStart_4244915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4244915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4244989 : List Nat := [1, 4, 1, 1, 1, 5, 1, 1, 1, 5, 2]
def baseStart_4244989 : Nat := 118140960795 + 4244989 * 2 ^ 59
def prefixEnd_4244989 : Nat := 4983230072969 + 3 ^ 40 * 4244989 * 2
def baseEnd_4244989 : Nat := 2179719730048797194715157

theorem tailTrace_4244989 : CollatzResearch.WordTrace tailWord_4244989 prefixEnd_4244989 2179719730048797194715157 := by
  unfold tailWord_4244989
  simp only [CollatzResearch.WordTrace]
  refine ⟨154827468418137314247194021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103218312278758209498129347 154827468418137314247194021)
  ·
    refine ⟨29030150328400746421348879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 154827468418137314247194021 29030150328400746421348879)
    ·
      refine ⟨43545225492601119632023319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29030150328400746421348879 43545225492601119632023319)
      ·
        refine ⟨65317838238901679448034979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43545225492601119632023319 65317838238901679448034979)
        ·
          refine ⟨97976757358352519172052469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65317838238901679448034979 97976757358352519172052469)
          ·
            refine ⟨9185321002345548672379919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 97976757358352519172052469 9185321002345548672379919)
            ·
              refine ⟨13777981503518323008569879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9185321002345548672379919 13777981503518323008569879)
              ·
                refine ⟨20666972255277484512854819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13777981503518323008569879 20666972255277484512854819)
                ·
                  refine ⟨31000458382916226769282229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20666972255277484512854819 31000458382916226769282229)
                  ·
                    refine ⟨2906292973398396259620209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31000458382916226769282229 2906292973398396259620209)
                    ·
                      refine ⟨2179719730048797194715157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2906292973398396259620209 2179719730048797194715157)
                      ·
                        rfl

theorem cell23_4244989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 5, 2].length) (baseStart_4244989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4244989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4244989 prefixEnd_4244989 := by exact prefixLift 4244989
  have htrace : WordTrace (prefixWord ++ tailWord_4244989) baseStart_4244989 baseEnd_4244989 := by
    simpa [prefixWord, tailWord_4244989, baseEnd_4244989] using wordTrace_append hprefix tailTrace_4244989
  have hstable : (prefixWord ++ tailWord_4244989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4244989).length < 2 ^ (prefixWord ++ tailWord_4244989).sum := by decide
  have hdescent : baseEnd_4244989 < baseStart_4244989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4244989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4244990 : List Nat := [4, 2, 2, 3, 1, 1, 2, 3, 1, 4]
def baseStart_4244990 : Nat := 118140960795 + 4244990 * 2 ^ 59
def prefixEnd_4244990 : Nat := 4983230072969 + 3 ^ 40 * 4244990 * 2
def baseEnd_4244990 : Nat := 726573414509817230267551

theorem tailTrace_4244990 : CollatzResearch.WordTrace tailWord_4244990 prefixEnd_4244990 726573414509817230267551 := by
  unfold tailWord_4244990
  simp only [CollatzResearch.WordTrace]
  refine ⟨19353438111391711427247553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103218336594089127611986949 19353438111391711427247553)
  ·
    refine ⟨14515078583543783570435665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19353438111391711427247553 14515078583543783570435665)
    ·
      refine ⟨10886308937657837677826749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14515078583543783570435665 10886308937657837677826749)
      ·
        refine ⟨4082365851621689129185031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10886308937657837677826749 4082365851621689129185031)
        ·
          refine ⟨6123548777432533693777547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4082365851621689129185031 6123548777432533693777547)
          ·
            refine ⟨9185323166148800540666321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6123548777432533693777547 9185323166148800540666321)
            ·
              refine ⟨6888992374611600405499741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9185323166148800540666321 6888992374611600405499741)
              ·
                refine ⟨2583372140479350152062403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6888992374611600405499741 2583372140479350152062403)
                ·
                  refine ⟨3875058210719025228093605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2583372140479350152062403 3875058210719025228093605)
                  ·
                    refine ⟨726573414509817230267551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3875058210719025228093605 726573414509817230267551)
                    ·
                      rfl

theorem cell23_4244990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_4244990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4244990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4244990 prefixEnd_4244990 := by exact prefixLift 4244990
  have htrace : WordTrace (prefixWord ++ tailWord_4244990) baseStart_4244990 baseEnd_4244990 := by
    simpa [prefixWord, tailWord_4244990, baseEnd_4244990] using wordTrace_append hprefix tailTrace_4244990
  have hstable : (prefixWord ++ tailWord_4244990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4244990).length < 2 ^ (prefixWord ++ tailWord_4244990).sum := by decide
  have hdescent : baseEnd_4244990 < baseStart_4244990 := by decide
  rcases family_descends (prefixWord ++ tailWord_4244990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4244995 : List Nat := [1, 1, 1, 3, 2, 1, 2, 3, 3, 6]
def baseStart_4244995 : Nat := 118140960795 + 4244995 * 2 ^ 59
def prefixEnd_4244995 : Nat := 4983230072969 + 3 ^ 40 * 4244995 * 2
def baseEnd_4244995 : Nat := 726574270310908057080043

theorem tailTrace_4244995 : CollatzResearch.WordTrace tailWord_4244995 prefixEnd_4244995 726574270310908057080043 := by
  unfold tailWord_4244995
  simp only [CollatzResearch.WordTrace]
  refine ⟨154827687256115577271912439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103218458170743718181274959 154827687256115577271912439)
  ·
    refine ⟨232241530884173365907868659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154827687256115577271912439 232241530884173365907868659)
    ·
      refine ⟨348362296326260048861802989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232241530884173365907868659 348362296326260048861802989)
      ·
        refine ⟨130635861122347518323176121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 348362296326260048861802989 130635861122347518323176121)
        ·
          refine ⟨97976895841760638742382091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130635861122347518323176121 97976895841760638742382091)
          ·
            refine ⟨146965343762640958113573137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97976895841760638742382091 146965343762640958113573137)
            ·
              refine ⟨110224007821980718585179853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146965343762640958113573137 110224007821980718585179853)
              ·
                refine ⟨41334002933242769469442445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110224007821980718585179853 41334002933242769469442445)
                ·
                  refine ⟨15500251099966038551040917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41334002933242769469442445 15500251099966038551040917)
                  ·
                    refine ⟨726574270310908057080043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15500251099966038551040917 726574270310908057080043)
                    ·
                      rfl

theorem cell23_4244995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 6].length) (baseStart_4244995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4244995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4244995 prefixEnd_4244995 := by exact prefixLift 4244995
  have htrace : WordTrace (prefixWord ++ tailWord_4244995) baseStart_4244995 baseEnd_4244995 := by
    simpa [prefixWord, tailWord_4244995, baseEnd_4244995] using wordTrace_append hprefix tailTrace_4244995
  have hstable : (prefixWord ++ tailWord_4244995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4244995).length < 2 ^ (prefixWord ++ tailWord_4244995).sum := by decide
  have hdescent : baseEnd_4244995 < baseStart_4244995 := by decide
  rcases family_descends (prefixWord ++ tailWord_4244995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4244999 : List Nat := [1, 1, 4, 3, 2, 2, 1, 3, 1, 5]
def baseStart_4244999 : Nat := 118140960795 + 4244999 * 2 ^ 59
def prefixEnd_4244999 : Nat := 4983230072969 + 3 ^ 40 * 4244999 * 2
def baseEnd_4244999 : Nat := 726574954951780718530037

theorem tailTrace_4244999 : CollatzResearch.WordTrace tailWord_4244999 prefixEnd_4244999 726574954951780718530037 := by
  unfold tailWord_4244999
  simp only [CollatzResearch.WordTrace]
  refine ⟨154827833148101085955058051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103218555432067390636705367 154827833148101085955058051)
  ·
    refine ⟨232241749722151628932587077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154827833148101085955058051 232241749722151628932587077)
    ·
      refine ⟨43545328072903430424860077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 232241749722151628932587077 43545328072903430424860077)
      ·
        refine ⟨16329498027338786409322529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43545328072903430424860077 16329498027338786409322529)
        ·
          refine ⟨12247123520504089806991897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16329498027338786409322529 12247123520504089806991897)
          ·
            refine ⟨9185342640378067355243923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12247123520504089806991897 9185342640378067355243923)
            ·
              refine ⟨13778013960567101032865885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9185342640378067355243923 13778013960567101032865885)
              ·
                refine ⟨5166755235212662887324707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13778013960567101032865885 5166755235212662887324707)
                ·
                  refine ⟨7750132852818994330987061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5166755235212662887324707 7750132852818994330987061)
                  ·
                    refine ⟨726574954951780718530037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7750132852818994330987061 726574954951780718530037)
                    ·
                      rfl

theorem cell23_4244999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 3, 1, 5].length) (baseStart_4244999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4244999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4244999 prefixEnd_4244999 := by exact prefixLift 4244999
  have htrace : WordTrace (prefixWord ++ tailWord_4244999) baseStart_4244999 baseEnd_4244999 := by
    simpa [prefixWord, tailWord_4244999, baseEnd_4244999] using wordTrace_append hprefix tailTrace_4244999
  have hstable : (prefixWord ++ tailWord_4244999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4244999).length < 2 ^ (prefixWord ++ tailWord_4244999).sum := by decide
  have hdescent : baseEnd_4244999 < baseStart_4244999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4244999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4245112 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 3, 6, 3]
def baseStart_4245112 : Nat := 118140960795 + 4245112 * 2 ^ 59
def prefixEnd_4245112 : Nat := 4983230072969 + 3 ^ 40 * 4245112 * 2
def baseEnd_4245112 : Nat := 2179782888169300213477091

theorem tailTrace_4245112 : CollatzResearch.WordTrace tailWord_4245112 prefixEnd_4245112 2179782888169300213477091 := by
  unfold tailWord_4245112
  simp only [CollatzResearch.WordTrace]
  refine ⟨77415977298345853126960795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103221303064461137502614393 77415977298345853126960795)
  ·
    refine ⟨116123965947518779690441193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77415977298345853126960795 116123965947518779690441193)
    ·
      refine ⟨87092974460639084767830895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116123965947518779690441193 87092974460639084767830895)
      ·
        refine ⟨130639461690958627151746343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87092974460639084767830895 130639461690958627151746343)
        ·
          refine ⟨195959192536437940727619515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130639461690958627151746343 195959192536437940727619515)
          ·
            refine ⟨293938788804656911091429273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195959192536437940727619515 293938788804656911091429273)
            ·
              refine ⟨220454091603492683318571955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 293938788804656911091429273 220454091603492683318571955)
              ·
                refine ⟨330681137405239024977857933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 220454091603492683318571955 330681137405239024977857933)
                ·
                  refine ⟨124005426526964634366696725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 330681137405239024977857933 124005426526964634366696725)
                  ·
                    refine ⟨5812754368451467235938909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 124005426526964634366696725 5812754368451467235938909)
                    ·
                      refine ⟨2179782888169300213477091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5812754368451467235938909 2179782888169300213477091)
                      ·
                        rfl

theorem cell23_4245112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 3, 6, 3].length) (baseStart_4245112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4245112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4245112 prefixEnd_4245112 := by exact prefixLift 4245112
  have htrace : WordTrace (prefixWord ++ tailWord_4245112) baseStart_4245112 baseEnd_4245112 := by
    simpa [prefixWord, tailWord_4245112, baseEnd_4245112] using wordTrace_append hprefix tailTrace_4245112
  have hstable : (prefixWord ++ tailWord_4245112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4245112).length < 2 ^ (prefixWord ++ tailWord_4245112).sum := by decide
  have hdescent : baseEnd_4245112 < baseStart_4245112 := by decide
  rcases family_descends (prefixWord ++ tailWord_4245112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4245113 : List Nat := [1, 2, 1, 3, 3, 1, 5, 1, 1, 3, 2]
def baseStart_4245113 : Nat := 118140960795 + 4245113 * 2 ^ 59
def prefixEnd_4245113 : Nat := 4983230072969 + 3 ^ 40 * 4245113 * 2
def baseEnd_4245113 : Nat := 2179783401649954709564587

theorem tailTrace_4245113 : CollatzResearch.WordTrace tailWord_4245113 prefixEnd_4245113 2179783401649954709564587 := by
  unfold tailWord_4245113
  simp only [CollatzResearch.WordTrace]
  refine ⟨154831991069688083424707993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103221327379792055616471995 154831991069688083424707993)
  ·
    refine ⟨116123993302266062568530995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154831991069688083424707993 116123993302266062568530995)
    ·
      refine ⟨174185989953399093852796493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116123993302266062568530995 174185989953399093852796493)
      ·
        refine ⟨65319746232524660194798685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 174185989953399093852796493 65319746232524660194798685)
        ·
          refine ⟨24494904837196747573049507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65319746232524660194798685 24494904837196747573049507)
          ·
            refine ⟨36742357255795121359574261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24494904837196747573049507 36742357255795121359574261)
            ·
              refine ⟨3444595992730792627460087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36742357255795121359574261 3444595992730792627460087)
              ·
                refine ⟨5166893989096188941190131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3444595992730792627460087 5166893989096188941190131)
                ·
                  refine ⟨7750340983644283411785197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5166893989096188941190131 7750340983644283411785197)
                  ·
                    refine ⟨2906377868866606279419449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7750340983644283411785197 2906377868866606279419449)
                    ·
                      refine ⟨2179783401649954709564587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2906377868866606279419449 2179783401649954709564587)
                      ·
                        rfl

theorem cell23_4245113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 1, 1, 3, 2].length) (baseStart_4245113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4245113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4245113 prefixEnd_4245113 := by exact prefixLift 4245113
  have htrace : WordTrace (prefixWord ++ tailWord_4245113) baseStart_4245113 baseEnd_4245113 := by
    simpa [prefixWord, tailWord_4245113, baseEnd_4245113] using wordTrace_append hprefix tailTrace_4245113
  have hstable : (prefixWord ++ tailWord_4245113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4245113).length < 2 ^ (prefixWord ++ tailWord_4245113).sum := by decide
  have hdescent : baseEnd_4245113 < baseStart_4245113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4245113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4245132 : List Nat := [2, 2, 1, 2, 1, 1, 4, 3, 7]
def baseStart_4245132 : Nat := 118140960795 + 4245132 * 2 ^ 59
def prefixEnd_4245132 : Nat := 4983230072969 + 3 ^ 40 * 4245132 * 2
def baseEnd_4245132 : Nat := 242199239753598903914111

theorem tailTrace_4245132 : CollatzResearch.WordTrace tailWord_4245132 prefixEnd_4245132 242199239753598903914111 := by
  unfold tailWord_4245132
  simp only [CollatzResearch.WordTrace]
  refine ⟨77416342028309624834824825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103221789371079499779766433 77416342028309624834824825)
  ·
    refine ⟨58062256521232218626118619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77416342028309624834824825 58062256521232218626118619)
    ·
      refine ⟨87093384781848327939177929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58062256521232218626118619 87093384781848327939177929)
      ·
        refine ⟨65320038586386245954383447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87093384781848327939177929 65320038586386245954383447)
        ·
          refine ⟨97980057879579368931575171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65320038586386245954383447 97980057879579368931575171)
          ·
            refine ⟨146970086819369053397362757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97980057879579368931575171 146970086819369053397362757)
            ·
              refine ⟨27556891278631697512005517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 146970086819369053397362757 27556891278631697512005517)
              ·
                refine ⟨10333834229486886567002069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27556891278631697512005517 10333834229486886567002069)
                ·
                  refine ⟨242199239753598903914111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10333834229486886567002069 242199239753598903914111)
                  ·
                    rfl

theorem cell23_4245132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 7].length) (baseStart_4245132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4245132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4245132 prefixEnd_4245132 := by exact prefixLift 4245132
  have htrace : WordTrace (prefixWord ++ tailWord_4245132) baseStart_4245132 baseEnd_4245132 := by
    simpa [prefixWord, tailWord_4245132, baseEnd_4245132] using wordTrace_append hprefix tailTrace_4245132
  have hstable : (prefixWord ++ tailWord_4245132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4245132).length < 2 ^ (prefixWord ++ tailWord_4245132).sum := by decide
  have hdescent : baseEnd_4245132 < baseStart_4245132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4245132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4245143 : List Nat := [1, 1, 3, 3, 2, 2, 2, 3, 2, 2, 2]
def baseStart_4245143 : Nat := 118140960795 + 4245143 * 2 ^ 59
def prefixEnd_4245143 : Nat := 4983230072969 + 3 ^ 40 * 4245143 * 2
def baseEnd_4245143 : Nat := 2179798806069589592189449

theorem tailTrace_4245143 : CollatzResearch.WordTrace tailWord_4245143 prefixEnd_4245143 2179798806069589592189449 := by
  unfold tailWord_4245143
  simp only [CollatzResearch.WordTrace]
  refine ⟨154833085259579398548300083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103222056839719599032200055 154833085259579398548300083)
  ·
    refine ⟨232249627889369097822450125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154833085259579398548300083 232249627889369097822450125)
    ·
      refine ⟨87093610458513411683418797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 232249627889369097822450125 87093610458513411683418797)
      ·
        refine ⟨32660103921942529381282049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87093610458513411683418797 32660103921942529381282049)
        ·
          refine ⟨24495077941456897035961537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32660103921942529381282049 24495077941456897035961537)
          ·
            refine ⟨18371308456092672776971153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24495077941456897035961537 18371308456092672776971153)
            ·
              refine ⟨13778481342069504582728365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18371308456092672776971153 13778481342069504582728365)
              ·
                refine ⟨5166930503276064218523137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13778481342069504582728365 5166930503276064218523137)
                ·
                  refine ⟨3875197877457048163892353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5166930503276064218523137 3875197877457048163892353)
                  ·
                    refine ⟨2906398408092786122919265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3875197877457048163892353 2906398408092786122919265)
                    ·
                      refine ⟨2179798806069589592189449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2906398408092786122919265 2179798806069589592189449)
                      ·
                        rfl

theorem cell23_4245143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 3, 2, 2, 2].length) (baseStart_4245143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4245143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4245143 prefixEnd_4245143 := by exact prefixLift 4245143
  have htrace : WordTrace (prefixWord ++ tailWord_4245143) baseStart_4245143 baseEnd_4245143 := by
    simpa [prefixWord, tailWord_4245143, baseEnd_4245143] using wordTrace_append hprefix tailTrace_4245143
  have hstable : (prefixWord ++ tailWord_4245143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4245143).length < 2 ^ (prefixWord ++ tailWord_4245143).sum := by decide
  have hdescent : baseEnd_4245143 < baseStart_4245143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4245143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4245289 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 7, 1, 4]
def baseStart_4245289 : Nat := 118140960795 + 4245289 * 2 ^ 59
def prefixEnd_4245289 : Nat := 4983230072969 + 3 ^ 40 * 4245289 * 2
def baseEnd_4245289 : Nat := 2179873774245146020963777

theorem tailTrace_4245289 : CollatzResearch.WordTrace tailWord_4245289 prefixEnd_4245289 2179873774245146020963777 := by
  unfold tailWord_4245289
  simp only [CollatzResearch.WordTrace]
  refine ⟨154838410317050465483114921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103225606878033643655409947 154838410317050465483114921)
  ·
    refine ⟨116128807737787849112336191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154838410317050465483114921 116128807737787849112336191)
    ·
      refine ⟨174193211606681773668504287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116128807737787849112336191 174193211606681773668504287)
      ·
        refine ⟨261289817410022660502756431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174193211606681773668504287 261289817410022660502756431)
        ·
          refine ⟨391934726115033990754134647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261289817410022660502756431 391934726115033990754134647)
          ·
            refine ⟨587902089172550986131201971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391934726115033990754134647 587902089172550986131201971)
            ·
              refine ⟨881853133758826479196802957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 587902089172550986131201971 881853133758826479196802957)
              ·
                refine ⟨330694925159559929698801109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 881853133758826479196802957 330694925159559929698801109)
                ·
                  refine ⟨7750662308427185852315651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 330694925159559929698801109 7750662308427185852315651)
                  ·
                    refine ⟨11625993462640778778473477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7750662308427185852315651 11625993462640778778473477)
                    ·
                      refine ⟨2179873774245146020963777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11625993462640778778473477 2179873774245146020963777)
                      ·
                        rfl

theorem cell23_4245289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 7, 1, 4].length) (baseStart_4245289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4245289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4245289 prefixEnd_4245289 := by exact prefixLift 4245289
  have htrace : WordTrace (prefixWord ++ tailWord_4245289) baseStart_4245289 baseEnd_4245289 := by
    simpa [prefixWord, tailWord_4245289, baseEnd_4245289] using wordTrace_append hprefix tailTrace_4245289
  have hstable : (prefixWord ++ tailWord_4245289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4245289).length < 2 ^ (prefixWord ++ tailWord_4245289).sum := by decide
  have hdescent : baseEnd_4245289 < baseStart_4245289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4245289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
