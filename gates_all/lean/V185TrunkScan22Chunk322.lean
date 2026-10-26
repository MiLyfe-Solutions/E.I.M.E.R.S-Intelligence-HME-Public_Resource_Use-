import V185TrunkScan22Chunk321

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2874369 : List Nat := [1, 2, 4, 1, 2, 3, 1, 1, 3, 4]
def baseStart_2874369 : Nat := 118140960795 + 2874369 * 2 ^ 59
def prefixEnd_2874369 : Nat := 4983230072969 + 3 ^ 40 * 2874369 * 2
def baseEnd_2874369 : Nat := 983955250255579834512349

theorem tailTrace_2874369 : CollatzResearch.WordTrace tailWord_2874369 prefixEnd_2874369 983955250255579834512349 := by
  unfold tailWord_2874369
  simp only [CollatzResearch.WordTrace]
  refine ⟨104836850123659490987514161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69891233415772993991676107 104836850123659490987514161)
  ·
    refine ⟨78627637592744618240635621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104836850123659490987514161 78627637592744618240635621)
    ·
      refine ⟨14742682048639615920119179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78627637592744618240635621 14742682048639615920119179)
      ·
        refine ⟨22114023072959423880178769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14742682048639615920119179 22114023072959423880178769)
        ·
          refine ⟨16585517304719567910134077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22114023072959423880178769 16585517304719567910134077)
          ·
            refine ⟨6219568989269837966300279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16585517304719567910134077 6219568989269837966300279)
            ·
              refine ⟨9329353483904756949450419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6219568989269837966300279 9329353483904756949450419)
              ·
                refine ⟨13994030225857135424175629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9329353483904756949450419 13994030225857135424175629)
                ·
                  refine ⟨5247761334696425784065861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13994030225857135424175629 5247761334696425784065861)
                  ·
                    refine ⟨983955250255579834512349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5247761334696425784065861 983955250255579834512349)
                    ·
                      rfl

theorem cell22_2874369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_2874369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2874369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2874369 prefixEnd_2874369 := by exact prefixLift 2874369
  have htrace : WordTrace (prefixWord ++ tailWord_2874369) baseStart_2874369 baseEnd_2874369 := by
    simpa [prefixWord, tailWord_2874369, baseEnd_2874369] using wordTrace_append hprefix tailTrace_2874369
  have hstable : (prefixWord ++ tailWord_2874369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874369).length < 2 ^ (prefixWord ++ tailWord_2874369).sum := by decide
  have hdescent : baseEnd_2874369 < baseStart_2874369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874401 : List Nat := [1, 2, 3, 2, 3, 2, 1, 4, 4]
def baseStart_2874401 : Nat := 118140960795 + 2874401 * 2 ^ 59
def prefixEnd_2874401 : Nat := 4983230072969 + 3 ^ 40 * 2874401 * 2
def baseEnd_2874401 : Nat := 327988734836514139237417

theorem tailTrace_2874401 : CollatzResearch.WordTrace tailWord_2874401 prefixEnd_2874401 327988734836514139237417 := by
  unfold tailWord_2874401
  simp only [CollatzResearch.WordTrace]
  refine ⟨104838017259543560452679057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69892011506362373635119371 104838017259543560452679057)
  ·
    refine ⟨78628512944657670339509293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104838017259543560452679057 78628512944657670339509293)
    ·
      refine ⟨29485692354246626377315985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78628512944657670339509293 29485692354246626377315985)
      ·
        refine ⟨22114269265684969782986989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29485692354246626377315985 22114269265684969782986989)
        ·
          refine ⟨8292850974631863668620121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22114269265684969782986989 8292850974631863668620121)
          ·
            refine ⟨6219638230973897751465091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8292850974631863668620121 6219638230973897751465091)
            ·
              refine ⟨9329457346460846627197637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6219638230973897751465091 9329457346460846627197637)
              ·
                refine ⟨1749273252461408742599557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9329457346460846627197637 1749273252461408742599557)
                ·
                  refine ⟨327988734836514139237417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1749273252461408742599557 327988734836514139237417)
                  ·
                    rfl

theorem cell22_2874401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 4, 4].length) (baseStart_2874401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2874401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2874401 prefixEnd_2874401 := by exact prefixLift 2874401
  have htrace : WordTrace (prefixWord ++ tailWord_2874401) baseStart_2874401 baseEnd_2874401 := by
    simpa [prefixWord, tailWord_2874401, baseEnd_2874401] using wordTrace_append hprefix tailTrace_2874401
  have hstable : (prefixWord ++ tailWord_2874401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874401).length < 2 ^ (prefixWord ++ tailWord_2874401).sum := by decide
  have hdescent : baseEnd_2874401 < baseStart_2874401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874414 : List Nat := [4, 1, 3, 1, 1, 1, 2, 2, 1, 6]
def baseStart_2874414 : Nat := 118140960795 + 2874414 * 2 ^ 59
def prefixEnd_2874414 : Nat := 4983230072969 + 3 ^ 40 * 2874414 * 2
def baseEnd_2874414 : Nat := 983970654675214717137211

theorem tailTrace_2874414 : CollatzResearch.WordTrace tailWord_2874414 prefixEnd_2874414 983970654675214717137211 := by
  unfold tailWord_2874414
  simp only [CollatzResearch.WordTrace]
  refine ⟨13104811426062057959112787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69892327605664309115268197 13104811426062057959112787)
  ·
    refine ⟨19657217139093086938669181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13104811426062057959112787 19657217139093086938669181)
    ·
      refine ⟨7371456427159907602000943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19657217139093086938669181 7371456427159907602000943)
      ·
        refine ⟨11057184640739861403001415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7371456427159907602000943 11057184640739861403001415)
        ·
          refine ⟨16585776961109792104502123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11057184640739861403001415 16585776961109792104502123)
          ·
            refine ⟨24878665441664688156753185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16585776961109792104502123 24878665441664688156753185)
            ·
              refine ⟨18658999081248516117564889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24878665441664688156753185 18658999081248516117564889)
              ·
                refine ⟨13994249310936387088173667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18658999081248516117564889 13994249310936387088173667)
                ·
                  refine ⟨20991373966404580632260501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13994249310936387088173667 20991373966404580632260501)
                  ·
                    refine ⟨983970654675214717137211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20991373966404580632260501 983970654675214717137211)
                    ·
                      rfl

theorem cell22_2874414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_2874414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2874414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2874414 prefixEnd_2874414 := by exact prefixLift 2874414
  have htrace : WordTrace (prefixWord ++ tailWord_2874414) baseStart_2874414 baseEnd_2874414 := by
    simpa [prefixWord, tailWord_2874414, baseEnd_2874414] using wordTrace_append hprefix tailTrace_2874414
  have hstable : (prefixWord ++ tailWord_2874414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874414).length < 2 ^ (prefixWord ++ tailWord_2874414).sum := by decide
  have hdescent : baseEnd_2874414 < baseStart_2874414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874444 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 7, 3]
def baseStart_2874444 : Nat := 118140960795 + 2874444 * 2 ^ 59
def prefixEnd_2874444 : Nat := 4983230072969 + 3 ^ 40 * 2874444 * 2
def baseEnd_2874444 : Nat := 983980924288304638887119

theorem tailTrace_2874444 : CollatzResearch.WordTrace tailWord_2874444 prefixEnd_2874444 983980924288304638887119 := by
  unfold tailWord_2874444
  simp only [CollatzResearch.WordTrace]
  refine ⟨52419792799193889398247193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69893057065591852530996257 52419792799193889398247193)
  ·
    refine ⟨39314844599395417048685395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52419792799193889398247193 39314844599395417048685395)
    ·
      refine ⟨58972266899093125573028093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39314844599395417048685395 58972266899093125573028093)
      ·
        refine ⟨22114600087159922089885535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58972266899093125573028093 22114600087159922089885535)
        ·
          refine ⟨33171900130739883134828303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22114600087159922089885535 33171900130739883134828303)
          ·
            refine ⟨49757850196109824702242455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33171900130739883134828303 49757850196109824702242455)
            ·
              refine ⟨74636775294164737053363683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49757850196109824702242455 74636775294164737053363683)
              ·
                refine ⟨111955162941247105580045525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74636775294164737053363683 111955162941247105580045525)
                ·
                  refine ⟨2623949131435479037032317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 111955162941247105580045525 2623949131435479037032317)
                  ·
                    refine ⟨983980924288304638887119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2623949131435479037032317 983980924288304638887119)
                    ·
                      rfl

theorem cell22_2874444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 7, 3].length) (baseStart_2874444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2874444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2874444 prefixEnd_2874444 := by exact prefixLift 2874444
  have htrace : WordTrace (prefixWord ++ tailWord_2874444) baseStart_2874444 baseEnd_2874444 := by
    simpa [prefixWord, tailWord_2874444, baseEnd_2874444] using wordTrace_append hprefix tailTrace_2874444
  have hstable : (prefixWord ++ tailWord_2874444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874444).length < 2 ^ (prefixWord ++ tailWord_2874444).sum := by decide
  have hdescent : baseEnd_2874444 < baseStart_2874444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874538 : List Nat := [3, 1, 5, 1, 1, 2, 1, 1, 3, 4]
def baseStart_2874538 : Nat := 118140960795 + 2874538 * 2 ^ 59
def prefixEnd_2874538 : Nat := 4983230072969 + 3 ^ 40 * 2874538 * 2
def baseEnd_2874538 : Nat := 984013102409319727036831

theorem tailTrace_2874538 : CollatzResearch.WordTrace tailWord_2874538 prefixEnd_2874538 984013102409319727036831 := by
  unfold tailWord_2874538
  simp only [CollatzResearch.WordTrace]
  refine ⟨26210753515011808212604067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69895342706698155233610845 26210753515011808212604067)
  ·
    refine ⟨39316130272517712318906101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26210753515011808212604067 39316130272517712318906101)
    ·
      refine ⟨3685887213048535529897447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39316130272517712318906101 3685887213048535529897447)
      ·
        refine ⟨5528830819572803294846171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3685887213048535529897447 5528830819572803294846171)
        ·
          refine ⟨8293246229359204942269257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5528830819572803294846171 8293246229359204942269257)
          ·
            refine ⟨6219934672019403706701943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8293246229359204942269257 6219934672019403706701943)
            ·
              refine ⟨9329902008029105560052915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6219934672019403706701943 9329902008029105560052915)
              ·
                refine ⟨13994853012043658340079373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9329902008029105560052915 13994853012043658340079373)
                ·
                  refine ⟨5248069879516371877529765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13994853012043658340079373 5248069879516371877529765)
                  ·
                    refine ⟨984013102409319727036831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5248069879516371877529765 984013102409319727036831)
                    ·
                      rfl

theorem cell22_2874538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_2874538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2874538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2874538 prefixEnd_2874538 := by exact prefixLift 2874538
  have htrace : WordTrace (prefixWord ++ tailWord_2874538) baseStart_2874538 baseEnd_2874538 := by
    simpa [prefixWord, tailWord_2874538, baseEnd_2874538] using wordTrace_append hprefix tailTrace_2874538
  have hstable : (prefixWord ++ tailWord_2874538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874538).length < 2 ^ (prefixWord ++ tailWord_2874538).sum := by decide
  have hdescent : baseEnd_2874538 < baseStart_2874538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874564 : List Nat := [2, 3, 3, 1, 13]
def baseStart_2874564 : Nat := 118140960795 + 2874564 * 2 ^ 59
def prefixEnd_2874564 : Nat := 4983230072969 + 3 ^ 40 * 2874564 * 2
def baseEnd_2874564 : Nat := 4049473262307260600357

theorem tailTrace_2874564 : CollatzResearch.WordTrace tailWord_2874564 prefixEnd_2874564 4049473262307260600357 := by
  unfold tailWord_2874564
  simp only [CollatzResearch.WordTrace]
  refine ⟨52421981178976519645431373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69895974905302026193908497 52421981178976519645431373)
  ·
    refine ⟨19658242942116194867036765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52421981178976519645431373 19658242942116194867036765)
    ·
      refine ⟨7371841103293573075138787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19658242942116194867036765 7371841103293573075138787)
      ·
        refine ⟨11057761654940359612708181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7371841103293573075138787 11057761654940359612708181)
        ·
          refine ⟨4049473262307260600357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 11057761654940359612708181 4049473262307260600357)
          ·
            rfl

theorem cell22_2874564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 13].length) (baseStart_2874564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2874564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2874564 prefixEnd_2874564 := by exact prefixLift 2874564
  have htrace : WordTrace (prefixWord ++ tailWord_2874564) baseStart_2874564 baseEnd_2874564 := by
    simpa [prefixWord, tailWord_2874564, baseEnd_2874564] using wordTrace_append hprefix tailTrace_2874564
  have hstable : (prefixWord ++ tailWord_2874564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874564).length < 2 ^ (prefixWord ++ tailWord_2874564).sum := by decide
  have hdescent : baseEnd_2874564 < baseStart_2874564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874570 : List Nat := [3, 1, 2, 1, 3, 4, 2, 2, 4]
def baseStart_2874570 : Nat := 118140960795 + 2874570 * 2 ^ 59
def prefixEnd_2874570 : Nat := 4983230072969 + 3 ^ 40 * 2874570 * 2
def baseEnd_2874570 : Nat := 328008018887760770078911

theorem tailTrace_2874570 : CollatzResearch.WordTrace tailWord_2874570 prefixEnd_2874570 328008018887760770078911 := by
  unfold tailWord_2874570
  simp only [CollatzResearch.WordTrace]
  refine ⟨26211045298982825578895291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69896120797287534877054109 26211045298982825578895291)
  ·
    refine ⟨39316567948474238368342937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26211045298982825578895291 39316567948474238368342937)
    ·
      refine ⟨29487425961355678776257203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39316567948474238368342937 29487425961355678776257203)
      ·
        refine ⟨44231138942033518164385805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29487425961355678776257203 44231138942033518164385805)
        ·
          refine ⟨16586677103262569311644677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44231138942033518164385805 16586677103262569311644677)
          ·
            refine ⟨3110001956861731745933377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16586677103262569311644677 3110001956861731745933377)
            ·
              refine ⟨2332501467646298809450033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3110001956861731745933377 2332501467646298809450033)
              ·
                refine ⟨1749376100734724107087525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2332501467646298809450033 1749376100734724107087525)
                ·
                  refine ⟨328008018887760770078911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1749376100734724107087525 328008018887760770078911)
                  ·
                    rfl

theorem cell22_2874570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 2, 4].length) (baseStart_2874570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2874570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2874570 prefixEnd_2874570 := by exact prefixLift 2874570
  have htrace : WordTrace (prefixWord ++ tailWord_2874570) baseStart_2874570 baseEnd_2874570 := by
    simpa [prefixWord, tailWord_2874570, baseEnd_2874570] using wordTrace_append hprefix tailTrace_2874570
  have hstable : (prefixWord ++ tailWord_2874570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874570).length < 2 ^ (prefixWord ++ tailWord_2874570).sum := by decide
  have hdescent : baseEnd_2874570 < baseStart_2874570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874581 : List Nat := [1, 3, 2, 4, 1, 1, 3, 7]
def baseStart_2874581 : Nat := 118140960795 + 2874581 * 2 ^ 59
def prefixEnd_2874581 : Nat := 4983230072969 + 3 ^ 40 * 2874581 * 2
def baseEnd_2874581 : Nat := 109336424687564660912411

theorem tailTrace_2874581 : CollatzResearch.WordTrace tailWord_2874581 prefixEnd_2874581 109336424687564660912411 := by
  unfold tailWord_2874581
  simp only [CollatzResearch.WordTrace]
  refine ⟨104844582398891451194231597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69896388265927634129487731 104844582398891451194231597)
  ·
    refine ⟨39316718399584294197836849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104844582398891451194231597 39316718399584294197836849)
    ·
      refine ⟨29487538799688220648377637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39316718399584294197836849 29487538799688220648377637)
      ·
        refine ⟨5528913524941541371570807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29487538799688220648377637 5528913524941541371570807)
        ·
          refine ⟨8293370287412312057356211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5528913524941541371570807 8293370287412312057356211)
          ·
            refine ⟨12440055431118468086034317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8293370287412312057356211 12440055431118468086034317)
            ·
              refine ⟨4665020786669425532262869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12440055431118468086034317 4665020786669425532262869)
              ·
                refine ⟨109336424687564660912411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4665020786669425532262869 109336424687564660912411)
                ·
                  rfl

theorem cell22_2874581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 7].length) (baseStart_2874581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2874581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2874581 prefixEnd_2874581 := by exact prefixLift 2874581
  have htrace : WordTrace (prefixWord ++ tailWord_2874581) baseStart_2874581 baseEnd_2874581 := by
    simpa [prefixWord, tailWord_2874581, baseEnd_2874581] using wordTrace_append hprefix tailTrace_2874581
  have hstable : (prefixWord ++ tailWord_2874581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874581).length < 2 ^ (prefixWord ++ tailWord_2874581).sum := by decide
  have hdescent : baseEnd_2874581 < baseStart_2874581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874596 : List Nat := [2, 3, 1, 1, 1, 2, 3, 1, 5, 3]
def baseStart_2874596 : Nat := 118140960795 + 2874596 * 2 ^ 59
def prefixEnd_2874596 : Nat := 4983230072969 + 3 ^ 40 * 2874596 * 2
def baseEnd_2874596 : Nat := 984032956994626909086653

theorem tailTrace_2874596 : CollatzResearch.WordTrace tailWord_2874596 prefixEnd_2874596 984032956994626909086653 := by
  unfold tailWord_2874596
  simp only [CollatzResearch.WordTrace]
  refine ⟨52422564746918554378013821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69896752995891405837351761 52422564746918554378013821)
  ·
    refine ⟨19658461780094457891755183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52422564746918554378013821 19658461780094457891755183)
    ·
      refine ⟨29487692670141686837632775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19658461780094457891755183 29487692670141686837632775)
      ·
        refine ⟨44231539005212530256449163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29487692670141686837632775 44231539005212530256449163)
        ·
          refine ⟨66347308507818795384673745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44231539005212530256449163 66347308507818795384673745)
          ·
            refine ⟨49760481380864096538505309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66347308507818795384673745 49760481380864096538505309)
            ·
              refine ⟨18660180517824036201939491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49760481380864096538505309 18660180517824036201939491)
              ·
                refine ⟨27990270776736054302909237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18660180517824036201939491 27990270776736054302909237)
                ·
                  refine ⟨2624087885319005090897741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27990270776736054302909237 2624087885319005090897741)
                  ·
                    refine ⟨984032956994626909086653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2624087885319005090897741 984032956994626909086653)
                    ·
                      rfl

theorem cell22_2874596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 5, 3].length) (baseStart_2874596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2874596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2874596 prefixEnd_2874596 := by exact prefixLift 2874596
  have htrace : WordTrace (prefixWord ++ tailWord_2874596) baseStart_2874596 baseEnd_2874596 := by
    simpa [prefixWord, tailWord_2874596, baseEnd_2874596] using wordTrace_append hprefix tailTrace_2874596
  have hstable : (prefixWord ++ tailWord_2874596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874596).length < 2 ^ (prefixWord ++ tailWord_2874596).sum := by decide
  have hdescent : baseEnd_2874596 < baseStart_2874596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874609 : List Nat := [1, 2, 2, 2, 2, 1, 1, 4, 7]
def baseStart_2874609 : Nat := 118140960795 + 2874609 * 2 ^ 59
def prefixEnd_2874609 : Nat := 4983230072969 + 3 ^ 40 * 2874609 * 2
def baseEnd_2874609 : Nat := 328012469053433069503871

theorem tailTrace_2874609 : CollatzResearch.WordTrace tailWord_2874609 prefixEnd_2874609 328012469053433069503871 := by
  unfold tailWord_2874609
  simp only [CollatzResearch.WordTrace]
  refine ⟨104845603642790011976250881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69897069095193341317500587 104845603642790011976250881)
  ·
    refine ⟨78634202732092508982188161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104845603642790011976250881 78634202732092508982188161)
    ·
      refine ⟨58975652049069381736641121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78634202732092508982188161 58975652049069381736641121)
      ·
        refine ⟨44231739036802036302480841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58975652049069381736641121 44231739036802036302480841)
        ·
          refine ⟨33173804277601527226860631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44231739036802036302480841 33173804277601527226860631)
          ·
            refine ⟨49760706416402290840290947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33173804277601527226860631 49760706416402290840290947)
            ·
              refine ⟨74641059624603436260436421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49760706416402290840290947 74641059624603436260436421)
              ·
                refine ⟨13995198679613144298831829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74641059624603436260436421 13995198679613144298831829)
                ·
                  refine ⟨328012469053433069503871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13995198679613144298831829 328012469053433069503871)
                  ·
                    rfl

theorem cell22_2874609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 7].length) (baseStart_2874609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2874609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2874609 prefixEnd_2874609 := by exact prefixLift 2874609
  have htrace : WordTrace (prefixWord ++ tailWord_2874609) baseStart_2874609 baseEnd_2874609 := by
    simpa [prefixWord, tailWord_2874609, baseEnd_2874609] using wordTrace_append hprefix tailTrace_2874609
  have hstable : (prefixWord ++ tailWord_2874609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874609).length < 2 ^ (prefixWord ++ tailWord_2874609).sum := by decide
  have hdescent : baseEnd_2874609 < baseStart_2874609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874673 : List Nat := [1, 2, 2, 3, 3, 1, 2, 3, 1, 4]
def baseStart_2874673 : Nat := 118140960795 + 2874673 * 2 ^ 59
def prefixEnd_2874673 : Nat := 4983230072969 + 3 ^ 40 * 2874673 * 2
def baseEnd_2874673 : Nat := 984059315668224374911417

theorem tailTrace_2874673 : CollatzResearch.WordTrace tailWord_2874673 prefixEnd_2874673 984059315668224374911417 := by
  unfold tailWord_2874673
  simp only [CollatzResearch.WordTrace]
  refine ⟨104847937914558150906580673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69898625276372100604387115 104847937914558150906580673)
  ·
    refine ⟨78635953435918613179935505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104847937914558150906580673 78635953435918613179935505)
    ·
      refine ⟨58976965076938959884951629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78635953435918613179935505 58976965076938959884951629)
      ·
        refine ⟨22116361903852109956856861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58976965076938959884951629 22116361903852109956856861)
        ·
          refine ⟨8293635713944541233821323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22116361903852109956856861 8293635713944541233821323)
          ·
            refine ⟨12440453570916811850731985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8293635713944541233821323 12440453570916811850731985)
            ·
              refine ⟨9330340178187608888048989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12440453570916811850731985 9330340178187608888048989)
              ·
                refine ⟨3498877566820353333018371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9330340178187608888048989 3498877566820353333018371)
                ·
                  refine ⟨5248316350230529999527557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3498877566820353333018371 5248316350230529999527557)
                  ·
                    refine ⟨984059315668224374911417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5248316350230529999527557 984059315668224374911417)
                    ·
                      rfl

theorem cell22_2874673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 3, 1, 4].length) (baseStart_2874673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2874673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2874673 prefixEnd_2874673 := by exact prefixLift 2874673
  have htrace : WordTrace (prefixWord ++ tailWord_2874673) baseStart_2874673 baseEnd_2874673 := by
    simpa [prefixWord, tailWord_2874673, baseEnd_2874673] using wordTrace_append hprefix tailTrace_2874673
  have hstable : (prefixWord ++ tailWord_2874673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874673).length < 2 ^ (prefixWord ++ tailWord_2874673).sum := by decide
  have hdescent : baseEnd_2874673 < baseStart_2874673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874748 : List Nat := [2, 2, 2, 1, 1, 1, 4, 3, 3, 3]
def baseStart_2874748 : Nat := 118140960795 + 2874748 * 2 ^ 59
def prefixEnd_2874748 : Nat := 4983230072969 + 3 ^ 40 * 2874748 * 2
def baseEnd_2874748 : Nat := 984084989700949179286187

theorem tailTrace_2874748 : CollatzResearch.WordTrace tailWord_2874748 prefixEnd_2874748 984084989700949179286187 := by
  unfold tailWord_2874748
  simp only [CollatzResearch.WordTrace]
  refine ⟨52425336694643219357780449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69900448926190959143707265 52425336694643219357780449)
  ·
    refine ⟨39319002520982414518335337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52425336694643219357780449 39319002520982414518335337)
    ·
      refine ⟨29489251890736810888751503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39319002520982414518335337 29489251890736810888751503)
      ·
        refine ⟨44233877836105216333127255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29489251890736810888751503 44233877836105216333127255)
        ·
          refine ⟨66350816754157824499690883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44233877836105216333127255 66350816754157824499690883)
          ·
            refine ⟨99526225131236736749536325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66350816754157824499690883 99526225131236736749536325)
            ·
              refine ⟨18661167212106888140538061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99526225131236736749536325 18661167212106888140538061)
              ·
                refine ⟨6997937704540083052701773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18661167212106888140538061 6997937704540083052701773)
                ·
                  refine ⟨2624226639202531144763165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6997937704540083052701773 2624226639202531144763165)
                  ·
                    refine ⟨984084989700949179286187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2624226639202531144763165 984084989700949179286187)
                    ·
                      rfl

theorem cell22_2874748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 3, 3].length) (baseStart_2874748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2874748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2874748 prefixEnd_2874748 := by exact prefixLift 2874748
  have htrace : WordTrace (prefixWord ++ tailWord_2874748) baseStart_2874748 baseEnd_2874748 := by
    simpa [prefixWord, tailWord_2874748, baseEnd_2874748] using wordTrace_append hprefix tailTrace_2874748
  have hstable : (prefixWord ++ tailWord_2874748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874748).length < 2 ^ (prefixWord ++ tailWord_2874748).sum := by decide
  have hdescent : baseEnd_2874748 < baseStart_2874748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874812 : List Nat := [2, 2, 2, 4, 2, 1, 3, 1, 5]
def baseStart_2874812 : Nat := 118140960795 + 2874812 * 2 ^ 59
def prefixEnd_2874812 : Nat := 4983230072969 + 3 ^ 40 * 2874812 * 2
def baseEnd_2874812 : Nat := 328035632736291448561997

theorem tailTrace_2874812 : CollatzResearch.WordTrace tailWord_2874812 prefixEnd_2874812 328035632736291448561997 := by
  unfold tailWord_2874812
  simp only [CollatzResearch.WordTrace]
  refine ⟨52426503830527288822945345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69902005107369718430593793 52426503830527288822945345)
  ·
    refine ⟨39319877872895466617209009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52426503830527288822945345 39319877872895466617209009)
    ·
      refine ⟨29489908404671599962906757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39319877872895466617209009 29489908404671599962906757)
      ·
        refine ⟨5529357825875924993045017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29489908404671599962906757 5529357825875924993045017)
        ·
          refine ⟨4147018369406943744783763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5529357825875924993045017 4147018369406943744783763)
          ·
            refine ⟨6220527554110415617175645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4147018369406943744783763 6220527554110415617175645)
            ·
              refine ⟨2332697832791405856440867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6220527554110415617175645 2332697832791405856440867)
              ·
                refine ⟨3499046749187108784661301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2332697832791405856440867 3499046749187108784661301)
                ·
                  refine ⟨328035632736291448561997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3499046749187108784661301 328035632736291448561997)
                  ·
                    rfl

theorem cell22_2874812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 1, 5].length) (baseStart_2874812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2874812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2874812 prefixEnd_2874812 := by exact prefixLift 2874812
  have htrace : WordTrace (prefixWord ++ tailWord_2874812) baseStart_2874812 baseEnd_2874812 := by
    simpa [prefixWord, tailWord_2874812, baseEnd_2874812] using wordTrace_append hprefix tailTrace_2874812
  have hstable : (prefixWord ++ tailWord_2874812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874812).length < 2 ^ (prefixWord ++ tailWord_2874812).sum := by decide
  have hdescent : baseEnd_2874812 < baseStart_2874812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874818 : List Nat := [3, 5, 2, 1, 2, 1, 2, 6]
def baseStart_2874818 : Nat := 118140960795 + 2874818 * 2 ^ 59
def prefixEnd_2874818 : Nat := 4983230072969 + 3 ^ 40 * 2874818 * 2
def baseEnd_2874818 : Nat := 109345439125721370003997

theorem tailTrace_2874818 : CollatzResearch.WordTrace tailWord_2874818 prefixEnd_2874818 109345439125721370003997 := by
  unfold tailWord_2874818
  simp only [CollatzResearch.WordTrace]
  refine ⟨26213306624758210167652277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69902150999355227113739405 26213306624758210167652277)
  ·
    refine ⟨2457497496071082203217401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26213306624758210167652277 2457497496071082203217401)
    ·
      refine ⟨1843123122053311652413051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2457497496071082203217401 1843123122053311652413051)
      ·
        refine ⟨2764684683079967478619577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1843123122053311652413051 2764684683079967478619577)
        ·
          refine ⟨2073513512309975608964683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2764684683079967478619577 2073513512309975608964683)
          ·
            refine ⟨3110270268464963413447025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2073513512309975608964683 3110270268464963413447025)
            ·
              refine ⟨2332702701348722560085269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3110270268464963413447025 2332702701348722560085269)
              ·
                refine ⟨109345439125721370003997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2332702701348722560085269 109345439125721370003997)
                ·
                  rfl

theorem cell22_2874818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 6].length) (baseStart_2874818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2874818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2874818 prefixEnd_2874818 := by exact prefixLift 2874818
  have htrace : WordTrace (prefixWord ++ tailWord_2874818) baseStart_2874818 baseEnd_2874818 := by
    simpa [prefixWord, tailWord_2874818, baseEnd_2874818] using wordTrace_append hprefix tailTrace_2874818
  have hstable : (prefixWord ++ tailWord_2874818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874818).length < 2 ^ (prefixWord ++ tailWord_2874818).sum := by decide
  have hdescent : baseEnd_2874818 < baseStart_2874818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874840 : List Nat := [2, 1, 2, 2, 2, 1, 5, 3, 4]
def baseStart_2874840 : Nat := 118140960795 + 2874840 * 2 ^ 59
def prefixEnd_2874840 : Nat := 4983230072969 + 3 ^ 40 * 2874840 * 2
def baseEnd_2874840 : Nat := 328038827727030535328635

theorem tailTrace_2874840 : CollatzResearch.WordTrace tailWord_2874840 prefixEnd_2874840 328038827727030535328635 := by
  unfold tailWord_2874840
  simp only [CollatzResearch.WordTrace]
  refine ⟨52427014452476569213954987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69902685936635425618606649 52427014452476569213954987)
  ·
    refine ⟨78640521678714853820932481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52427014452476569213954987 78640521678714853820932481)
    ·
      refine ⟨58980391259036140365699361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78640521678714853820932481 58980391259036140365699361)
      ·
        refine ⟨44235293444277105274274521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58980391259036140365699361 44235293444277105274274521)
        ·
          refine ⟨33176470083207828955705891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44235293444277105274274521 33176470083207828955705891)
          ·
            refine ⟨49764705124811743433558837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33176470083207828955705891 49764705124811743433558837)
            ·
              refine ⟨4665441105451100946896141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49764705124811743433558837 4665441105451100946896141)
              ·
                refine ⟨1749540414544162855086053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4665441105451100946896141 1749540414544162855086053)
                ·
                  refine ⟨328038827727030535328635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1749540414544162855086053 328038827727030535328635)
                  ·
                    rfl

theorem cell22_2874840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 3, 4].length) (baseStart_2874840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2874840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2874840 prefixEnd_2874840 := by exact prefixLift 2874840
  have htrace : WordTrace (prefixWord ++ tailWord_2874840) baseStart_2874840 baseEnd_2874840 := by
    simpa [prefixWord, tailWord_2874840, baseEnd_2874840] using wordTrace_append hprefix tailTrace_2874840
  have hstable : (prefixWord ++ tailWord_2874840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874840).length < 2 ^ (prefixWord ++ tailWord_2874840).sum := by decide
  have hdescent : baseEnd_2874840 < baseStart_2874840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874855 : List Nat := [1, 1, 5, 2, 1, 2, 2, 1, 4, 3]
def baseStart_2874855 : Nat := 118140960795 + 2874855 * 2 ^ 59
def prefixEnd_2874855 : Nat := 4983230072969 + 3 ^ 40 * 2874855 * 2
def baseEnd_2874855 : Nat := 984121617987636566860859

theorem tailTrace_2874855 : CollatzResearch.WordTrace tailWord_2874855 prefixEnd_2874855 984121617987636566860859 := by
  unfold tailWord_2874855
  simp only [CollatzResearch.WordTrace]
  refine ⟨104854575999898795989706019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69903050666599197326470679 104854575999898795989706019)
  ·
    refine ⟨157281863999848193984559029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104854575999898795989706019 157281863999848193984559029)
    ·
      refine ⟨14745174749985768186052409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 157281863999848193984559029 14745174749985768186052409)
      ·
        refine ⟨11058881062489326139539307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14745174749985768186052409 11058881062489326139539307)
        ·
          refine ⟨16588321593733989209308961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11058881062489326139539307 16588321593733989209308961)
          ·
            refine ⟨12441241195300491906981721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16588321593733989209308961 12441241195300491906981721)
            ·
              refine ⟨9330930896475368930236291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12441241195300491906981721 9330930896475368930236291)
              ·
                refine ⟨13996396344713053395354437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9330930896475368930236291 13996396344713053395354437)
                ·
                  refine ⟨2624324314633697511628957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13996396344713053395354437 2624324314633697511628957)
                  ·
                    refine ⟨984121617987636566860859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2624324314633697511628957 984121617987636566860859)
                    ·
                      rfl

theorem cell22_2874855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_2874855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2874855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2874855 prefixEnd_2874855 := by exact prefixLift 2874855
  have htrace : WordTrace (prefixWord ++ tailWord_2874855) baseStart_2874855 baseEnd_2874855 := by
    simpa [prefixWord, tailWord_2874855, baseEnd_2874855] using wordTrace_append hprefix tailTrace_2874855
  have hstable : (prefixWord ++ tailWord_2874855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874855).length < 2 ^ (prefixWord ++ tailWord_2874855).sum := by decide
  have hdescent : baseEnd_2874855 < baseStart_2874855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874872 : List Nat := [2, 1, 2, 1, 1, 5, 4, 1, 2, 3]
def baseStart_2874872 : Nat := 118140960795 + 2874872 * 2 ^ 59
def prefixEnd_2874872 : Nat := 4983230072969 + 3 ^ 40 * 2874872 * 2
def baseEnd_2874872 : Nat := 984127437435054189185807

theorem tailTrace_2874872 : CollatzResearch.WordTrace tailWord_2874872 prefixEnd_2874872 984127437435054189185807 := by
  unfold tailWord_2874872
  simp only [CollatzResearch.WordTrace]
  refine ⟨52427598020418603946537435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69903464027224805262049913 52427598020418603946537435)
  ·
    refine ⟨78641397030627905919806153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52427598020418603946537435 78641397030627905919806153)
    ·
      refine ⟨58981047772970929439854615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78641397030627905919806153 58981047772970929439854615)
      ·
        refine ⟨88471571659456394159781923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58981047772970929439854615 88471571659456394159781923)
        ·
          refine ⟨132707357489184591239672885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88471571659456394159781923 132707357489184591239672885)
          ·
            refine ⟨12441314764611055428719333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 132707357489184591239672885 12441314764611055428719333)
            ·
              refine ⟨2332746518364572892884875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12441314764611055428719333 2332746518364572892884875)
              ·
                refine ⟨3499119777546859339327313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2332746518364572892884875 3499119777546859339327313)
                ·
                  refine ⟨2624339833160144504495485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3499119777546859339327313 2624339833160144504495485)
                  ·
                    refine ⟨984127437435054189185807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2624339833160144504495485 984127437435054189185807)
                    ·
                      rfl

theorem cell22_2874872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 1, 2, 3].length) (baseStart_2874872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2874872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2874872 prefixEnd_2874872 := by exact prefixLift 2874872
  have htrace : WordTrace (prefixWord ++ tailWord_2874872) baseStart_2874872 baseEnd_2874872 := by
    simpa [prefixWord, tailWord_2874872, baseEnd_2874872] using wordTrace_append hprefix tailTrace_2874872
  have hstable : (prefixWord ++ tailWord_2874872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874872).length < 2 ^ (prefixWord ++ tailWord_2874872).sum := by decide
  have hdescent : baseEnd_2874872 < baseStart_2874872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874934 : List Nat := [5, 1, 2, 1, 3, 1, 1, 2, 3, 3]
def baseStart_2874934 : Nat := 118140960795 + 2874934 * 2 ^ 59
def prefixEnd_2874934 : Nat := 4983230072969 + 3 ^ 40 * 2874934 * 2
def baseEnd_2874934 : Nat := 984148661302106694135617

theorem tailTrace_2874934 : CollatzResearch.WordTrace tailWord_2874934 prefixEnd_2874934 984148661302106694135617 := by
  unfold tailWord_2874934
  simp only [CollatzResearch.WordTrace]
  refine ⟨6553591085413287030114491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69904971577741728321221237 6553591085413287030114491)
  ·
    refine ⟨9830386628119930545171737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6553591085413287030114491 9830386628119930545171737)
    ·
      refine ⟨7372789971089947908878803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9830386628119930545171737 7372789971089947908878803)
      ·
        refine ⟨11059184956634921863318205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7372789971089947908878803 11059184956634921863318205)
        ·
          refine ⟨4147194358738095698744327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11059184956634921863318205 4147194358738095698744327)
          ·
            refine ⟨6220791538107143548116491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4147194358738095698744327 6220791538107143548116491)
            ·
              refine ⟨9331187307160715322174737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6220791538107143548116491 9331187307160715322174737)
              ·
                refine ⟨6998390480370536491631053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9331187307160715322174737 6998390480370536491631053)
                ·
                  refine ⟨2624396430138951184361645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6998390480370536491631053 2624396430138951184361645)
                  ·
                    refine ⟨984148661302106694135617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2624396430138951184361645 984148661302106694135617)
                    ·
                      rfl

theorem cell22_2874934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_2874934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2874934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2874934 prefixEnd_2874934 := by exact prefixLift 2874934
  have htrace : WordTrace (prefixWord ++ tailWord_2874934) baseStart_2874934 baseEnd_2874934 := by
    simpa [prefixWord, tailWord_2874934, baseEnd_2874934] using wordTrace_append hprefix tailTrace_2874934
  have hstable : (prefixWord ++ tailWord_2874934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874934).length < 2 ^ (prefixWord ++ tailWord_2874934).sum := by decide
  have hdescent : baseEnd_2874934 < baseStart_2874934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874958 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 10]
def baseStart_2874958 : Nat := 118140960795 + 2874958 * 2 ^ 59
def prefixEnd_2874958 : Nat := 4983230072969 + 3 ^ 40 * 2874958 * 2
def baseEnd_2874958 : Nat := 328052292330859543845181

theorem tailTrace_2874958 : CollatzResearch.WordTrace tailWord_2874958 prefixEnd_2874958 328052292330859543845181 := by
  unfold tailWord_2874958
  simp only [CollatzResearch.WordTrace]
  refine ⟨13107291589815705572588191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69905555145683763053803685 13107291589815705572588191)
  ·
    refine ⟨19660937384723558358882287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13107291589815705572588191 19660937384723558358882287)
    ·
      refine ⟨29491406077085337538323431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19660937384723558358882287 29491406077085337538323431)
      ·
        refine ⟨44237109115628006307485147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29491406077085337538323431 44237109115628006307485147)
        ·
          refine ⟨66355663673442009461227721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44237109115628006307485147 66355663673442009461227721)
          ·
            refine ⟨49766747755081507095920791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66355663673442009461227721 49766747755081507095920791)
            ·
              refine ⟨74650121632622260643881187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49766747755081507095920791 74650121632622260643881187)
              ·
                refine ⟨111975182448933390965821781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74650121632622260643881187 111975182448933390965821781)
                ·
                  refine ⟨328052292330859543845181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 111975182448933390965821781 328052292330859543845181)
                  ·
                    rfl

theorem cell22_2874958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 10].length) (baseStart_2874958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2874958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2874958 prefixEnd_2874958 := by exact prefixLift 2874958
  have htrace : WordTrace (prefixWord ++ tailWord_2874958) baseStart_2874958 baseEnd_2874958 := by
    simpa [prefixWord, tailWord_2874958, baseEnd_2874958] using wordTrace_append hprefix tailTrace_2874958
  have hstable : (prefixWord ++ tailWord_2874958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874958).length < 2 ^ (prefixWord ++ tailWord_2874958).sum := by decide
  have hdescent : baseEnd_2874958 < baseStart_2874958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2874960 : List Nat := [2, 1, 1, 1, 1, 3, 5, 3, 1, 4]
def baseStart_2874960 : Nat := 118140960795 + 2874960 * 2 ^ 59
def prefixEnd_2874960 : Nat := 4983230072969 + 3 ^ 40 * 2874960 * 2
def baseEnd_2874960 : Nat := 984157561633451292985537

theorem tailTrace_2874960 : CollatzResearch.WordTrace tailWord_2874960 prefixEnd_2874960 984157561633451292985537 := by
  unfold tailWord_2874960
  simp only [CollatzResearch.WordTrace]
  refine ⟨52429202832259199461139167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69905603776345599281518889 52429202832259199461139167)
  ·
    refine ⟨78643804248388799191708751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52429202832259199461139167 78643804248388799191708751)
    ·
      refine ⟨117965706372583198787563127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78643804248388799191708751 117965706372583198787563127)
      ·
        refine ⟨176948559558874798181344691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117965706372583198787563127 176948559558874798181344691)
        ·
          refine ⟨265422839338312197272017037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176948559558874798181344691 265422839338312197272017037)
          ·
            refine ⟨99533564751867073977006389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 265422839338312197272017037 99533564751867073977006389)
            ·
              refine ⟨9331271695487538185344349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 99533564751867073977006389 9331271695487538185344349)
              ·
                refine ⟨3499226885807826819504131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9331271695487538185344349 3499226885807826819504131)
                ·
                  refine ⟨5248840328711740229256197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3499226885807826819504131 5248840328711740229256197)
                  ·
                    refine ⟨984157561633451292985537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5248840328711740229256197 984157561633451292985537)
                    ·
                      rfl

theorem cell22_2874960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 3, 1, 4].length) (baseStart_2874960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2874960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2874960 prefixEnd_2874960 := by exact prefixLift 2874960
  have htrace : WordTrace (prefixWord ++ tailWord_2874960) baseStart_2874960 baseEnd_2874960 := by
    simpa [prefixWord, tailWord_2874960, baseEnd_2874960] using wordTrace_append hprefix tailTrace_2874960
  have hstable : (prefixWord ++ tailWord_2874960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2874960).length < 2 ^ (prefixWord ++ tailWord_2874960).sum := by decide
  have hdescent : baseEnd_2874960 < baseStart_2874960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2874960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875003 : List Nat := [1, 1, 1, 1, 1, 4, 5, 8]
def baseStart_2875003 : Nat := 118140960795 + 2875003 * 2 ^ 59
def prefixEnd_2875003 : Nat := 4983230072969 + 3 ^ 40 * 2875003 * 2
def baseEnd_2875003 : Nat := 109352475712468168240045

theorem tailTrace_2875003 : CollatzResearch.WordTrace tailWord_2875003 prefixEnd_2875003 109352475712468168240045 := by
  unfold tailWord_2875003
  simp only [CollatzResearch.WordTrace]
  refine ⟨104859974003362617266093663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69906649335575078177395775 104859974003362617266093663)
  ·
    refine ⟨157289961005043925899140495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104859974003362617266093663 157289961005043925899140495)
    ·
      refine ⟨235934941507565888848710743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157289961005043925899140495 235934941507565888848710743)
      ·
        refine ⟨353902412261348833273066115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235934941507565888848710743 353902412261348833273066115)
        ·
          refine ⟨530853618392023249909599173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353902412261348833273066115 530853618392023249909599173)
          ·
            refine ⟨99535053448504359358049845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 530853618392023249909599173 99535053448504359358049845)
            ·
              refine ⟨9331411260797283689817173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 99535053448504359358049845 9331411260797283689817173)
              ·
                refine ⟨109352475712468168240045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9331411260797283689817173 109352475712468168240045)
                ·
                  rfl

theorem cell22_2875003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 8].length) (baseStart_2875003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2875003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2875003 prefixEnd_2875003 := by exact prefixLift 2875003
  have htrace : WordTrace (prefixWord ++ tailWord_2875003) baseStart_2875003 baseEnd_2875003 := by
    simpa [prefixWord, tailWord_2875003, baseEnd_2875003] using wordTrace_append hprefix tailTrace_2875003
  have hstable : (prefixWord ++ tailWord_2875003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875003).length < 2 ^ (prefixWord ++ tailWord_2875003).sum := by decide
  have hdescent : baseEnd_2875003 < baseStart_2875003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875005 : List Nat := [1, 4, 1, 1, 4, 1, 2, 1, 1, 6]
def baseStart_2875005 : Nat := 118140960795 + 2875005 * 2 ^ 59
def prefixEnd_2875005 : Nat := 4983230072969 + 3 ^ 40 * 2875005 * 2
def baseEnd_2875005 : Nat := 984172966053086175610399

theorem tailTrace_2875005 : CollatzResearch.WordTrace tailWord_2875005 prefixEnd_2875005 984172966053086175610399 := by
  unfold tailWord_2875005
  simp only [CollatzResearch.WordTrace]
  refine ⟨104860046949355371607666469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69906697966236914405110979 104860046949355371607666469)
  ·
    refine ⟨19661258803004132176437463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104860046949355371607666469 19661258803004132176437463)
    ·
      refine ⟨29491888204506198264656195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19661258803004132176437463 29491888204506198264656195)
      ·
        refine ⟨44237832306759297396984293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29491888204506198264656195 44237832306759297396984293)
        ·
          refine ⟨8294593557517368261934555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44237832306759297396984293 8294593557517368261934555)
          ·
            refine ⟨12441890336276052392901833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8294593557517368261934555 12441890336276052392901833)
            ·
              refine ⟨9331417752207039294676375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12441890336276052392901833 9331417752207039294676375)
              ·
                refine ⟨13997126628310558942014563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9331417752207039294676375 13997126628310558942014563)
                ·
                  refine ⟨20995689942465838413021845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13997126628310558942014563 20995689942465838413021845)
                  ·
                    refine ⟨984172966053086175610399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20995689942465838413021845 984172966053086175610399)
                    ·
                      rfl

theorem cell22_2875005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_2875005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2875005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2875005 prefixEnd_2875005 := by exact prefixLift 2875005
  have htrace : WordTrace (prefixWord ++ tailWord_2875005) baseStart_2875005 baseEnd_2875005 := by
    simpa [prefixWord, tailWord_2875005, baseEnd_2875005] using wordTrace_append hprefix tailTrace_2875005
  have hstable : (prefixWord ++ tailWord_2875005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875005).length < 2 ^ (prefixWord ++ tailWord_2875005).sum := by decide
  have hdescent : baseEnd_2875005 < baseStart_2875005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875009 : List Nat := [1, 2, 4, 2, 1, 4, 1, 3, 4]
def baseStart_2875009 : Nat := 118140960795 + 2875009 * 2 ^ 59
def prefixEnd_2875009 : Nat := 4983230072969 + 3 ^ 40 * 2875009 * 2
def baseEnd_2875009 : Nat := 328058111778277166170129

theorem tailTrace_2875009 : CollatzResearch.WordTrace tailWord_2875009 prefixEnd_2875009 328058111778277166170129 := by
  unfold tailWord_2875009
  simp only [CollatzResearch.WordTrace]
  refine ⟨104860192841340880290812081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69906795227560586860541387 104860192841340880290812081)
  ·
    refine ⟨78645144631005660218109061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104860192841340880290812081 78645144631005660218109061)
    ·
      refine ⟨14745964618313561290895449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78645144631005660218109061 14745964618313561290895449)
      ·
        refine ⟨11059473463735170968171587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14745964618313561290895449 11059473463735170968171587)
        ·
          refine ⟨16589210195602756452257381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11059473463735170968171587 16589210195602756452257381)
          ·
            refine ⟨3110476911675516834798259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16589210195602756452257381 3110476911675516834798259)
            ·
              refine ⟨4665715367513275252197389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3110476911675516834798259 4665715367513275252197389)
              ·
                refine ⟨1749643262817478219574021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4665715367513275252197389 1749643262817478219574021)
                ·
                  refine ⟨328058111778277166170129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1749643262817478219574021 328058111778277166170129)
                  ·
                    rfl

theorem cell22_2875009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 3, 4].length) (baseStart_2875009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2875009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2875009 prefixEnd_2875009 := by exact prefixLift 2875009
  have htrace : WordTrace (prefixWord ++ tailWord_2875009) baseStart_2875009 baseEnd_2875009 := by
    simpa [prefixWord, tailWord_2875009, baseEnd_2875009] using wordTrace_append hprefix tailTrace_2875009
  have hstable : (prefixWord ++ tailWord_2875009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875009).length < 2 ^ (prefixWord ++ tailWord_2875009).sum := by decide
  have hdescent : baseEnd_2875009 < baseStart_2875009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875022 : List Nat := [4, 1, 1, 3, 1, 3, 1, 2, 2, 4]
def baseStart_2875022 : Nat := 118140960795 + 2875022 * 2 ^ 59
def prefixEnd_2875022 : Nat := 4983230072969 + 3 ^ 40 * 2875022 * 2
def baseEnd_2875022 : Nat := 984178785500503797935347

theorem tailTrace_2875022 : CollatzResearch.WordTrace tailWord_2875022 prefixEnd_2875022 984178785500503797935347 := by
  unfold tailWord_2875022
  simp only [CollatzResearch.WordTrace]
  refine ⟨13107583373786722938879415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69907111326862522340690213 13107583373786722938879415)
  ·
    refine ⟨19661375060680084408319123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13107583373786722938879415 19661375060680084408319123)
    ·
      refine ⟨29492062591020126612478685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19661375060680084408319123 29492062591020126612478685)
      ·
        refine ⟨11059523471632547479679507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29492062591020126612478685 11059523471632547479679507)
        ·
          refine ⟨16589285207448821219519261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11059523471632547479679507 16589285207448821219519261)
          ·
            refine ⟨6220981952793307957319723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16589285207448821219519261 6220981952793307957319723)
            ·
              refine ⟨9331472929189961935979585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6220981952793307957319723 9331472929189961935979585)
              ·
                refine ⟨6998604696892471451984689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9331472929189961935979585 6998604696892471451984689)
                ·
                  refine ⟨5248953522669353588988517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6998604696892471451984689 5248953522669353588988517)
                  ·
                    refine ⟨984178785500503797935347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5248953522669353588988517 984178785500503797935347)
                    ·
                      rfl

theorem cell22_2875022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_2875022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2875022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2875022 prefixEnd_2875022 := by exact prefixLift 2875022
  have htrace : WordTrace (prefixWord ++ tailWord_2875022) baseStart_2875022 baseEnd_2875022 := by
    simpa [prefixWord, tailWord_2875022, baseEnd_2875022] using wordTrace_append hprefix tailTrace_2875022
  have hstable : (prefixWord ++ tailWord_2875022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875022).length < 2 ^ (prefixWord ++ tailWord_2875022).sum := by decide
  have hdescent : baseEnd_2875022 < baseStart_2875022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875026 : List Nat := [3, 2, 3, 1, 3, 1, 3, 2, 4]
def baseStart_2875026 : Nat := 118140960795 + 2875026 * 2 ^ 59
def prefixEnd_2875026 : Nat := 4983230072969 + 3 ^ 40 * 2875026 * 2
def baseEnd_2875026 : Nat := 328060051594083040278445

theorem tailTrace_2875026 : CollatzResearch.WordTrace tailWord_2875026 prefixEnd_2875026 328060051594083040278445 := by
  unfold tailWord_2875026
  simp only [CollatzResearch.WordTrace]
  refine ⟨26215203220569823048545233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69907208588186194796120621 26215203220569823048545233)
  ·
    refine ⟨19661402415427367286408925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26215203220569823048545233 19661402415427367286408925)
    ·
      refine ⟨7373025905785262732403347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19661402415427367286408925 7373025905785262732403347)
      ·
        refine ⟨11059538858677894098605021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7373025905785262732403347 11059538858677894098605021)
        ·
          refine ⟨4147327072004210286976883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11059538858677894098605021 4147327072004210286976883)
          ·
            refine ⟨6220990608006315430465325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4147327072004210286976883 6220990608006315430465325)
            ·
              refine ⟨2332871478002368286424497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6220990608006315430465325 2332871478002368286424497)
              ·
                refine ⟨1749653608501776214818373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2332871478002368286424497 1749653608501776214818373)
                ·
                  refine ⟨328060051594083040278445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1749653608501776214818373 328060051594083040278445)
                  ·
                    rfl

theorem cell22_2875026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 2, 4].length) (baseStart_2875026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2875026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2875026 prefixEnd_2875026 := by exact prefixLift 2875026
  have htrace : WordTrace (prefixWord ++ tailWord_2875026) baseStart_2875026 baseEnd_2875026 := by
    simpa [prefixWord, tailWord_2875026, baseEnd_2875026] using wordTrace_append hprefix tailTrace_2875026
  have hstable : (prefixWord ++ tailWord_2875026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875026).length < 2 ^ (prefixWord ++ tailWord_2875026).sum := by decide
  have hdescent : baseEnd_2875026 < baseStart_2875026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875041 : List Nat := [1, 2, 3, 3, 2, 3, 2, 1, 2, 3]
def baseStart_2875041 : Nat := 118140960795 + 2875041 * 2 ^ 59
def prefixEnd_2875041 : Nat := 4983230072969 + 3 ^ 40 * 2875041 * 2
def baseEnd_2875041 : Nat := 984185289588794081710289

theorem tailTrace_2875041 : CollatzResearch.WordTrace tailWord_2875041 prefixEnd_2875041 984185289588794081710289 := by
  unfold tailWord_2875041
  simp only [CollatzResearch.WordTrace]
  refine ⟨104861359977224949755976977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69907573318149966503984651 104861359977224949755976977)
  ·
    refine ⟨78646019982918712316982733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104861359977224949755976977 78646019982918712316982733)
    ·
      refine ⟨29492257493594517118868525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78646019982918712316982733 29492257493594517118868525)
      ·
        refine ⟨11059596560097943919575697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29492257493594517118868525 11059596560097943919575697)
        ·
          refine ⟨8294697420073457939681773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11059596560097943919575697 8294697420073457939681773)
          ·
            refine ⟨3110511532527546727380665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8294697420073457939681773 3110511532527546727380665)
            ·
              refine ⟨2332883649395660045535499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3110511532527546727380665 2332883649395660045535499)
              ·
                refine ⟨3499325474093490068303249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2332883649395660045535499 3499325474093490068303249)
                ·
                  refine ⟨2624494105570117551227437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3499325474093490068303249 2624494105570117551227437)
                  ·
                    refine ⟨984185289588794081710289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2624494105570117551227437 984185289588794081710289)
                    ·
                      rfl

theorem cell22_2875041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 1, 2, 3].length) (baseStart_2875041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2875041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2875041 prefixEnd_2875041 := by exact prefixLift 2875041
  have htrace : WordTrace (prefixWord ++ tailWord_2875041) baseStart_2875041 baseEnd_2875041 := by
    simpa [prefixWord, tailWord_2875041, baseEnd_2875041] using wordTrace_append hprefix tailTrace_2875041
  have hstable : (prefixWord ++ tailWord_2875041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875041).length < 2 ^ (prefixWord ++ tailWord_2875041).sum := by decide
  have hdescent : baseEnd_2875041 < baseStart_2875041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875069 : List Nat := [1, 4, 1, 2, 1, 2, 2, 5, 1, 3]
def baseStart_2875069 : Nat := 118140960795 + 2875069 * 2 ^ 59
def prefixEnd_2875069 : Nat := 4983230072969 + 3 ^ 40 * 2875069 * 2
def baseEnd_2875069 : Nat := 984194874561011342010203

theorem tailTrace_2875069 : CollatzResearch.WordTrace tailWord_2875069 prefixEnd_2875069 984194874561011342010203 := by
  unfold tailWord_2875069
  simp only [CollatzResearch.WordTrace]
  refine ⟨104862381221123510537996261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69908254147415673691997507 104862381221123510537996261)
  ·
    refine ⟨19661696478960658225874299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104862381221123510537996261 19661696478960658225874299)
    ·
      refine ⟨29492544718440987338811449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19661696478960658225874299 29492544718440987338811449)
      ·
        refine ⟨22119408538830740504108587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29492544718440987338811449 22119408538830740504108587)
        ·
          refine ⟨33179112808246110756162881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22119408538830740504108587 33179112808246110756162881)
          ·
            refine ⟨24884334606184583067122161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33179112808246110756162881 24884334606184583067122161)
            ·
              refine ⟨18663250954638437300341621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24884334606184583067122161 18663250954638437300341621)
              ·
                refine ⟨1749679776997353496907027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18663250954638437300341621 1749679776997353496907027)
                ·
                  refine ⟨2624519665496030245360541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1749679776997353496907027 2624519665496030245360541)
                  ·
                    refine ⟨984194874561011342010203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2624519665496030245360541 984194874561011342010203)
                    ·
                      rfl

theorem cell22_2875069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 5, 1, 3].length) (baseStart_2875069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2875069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2875069 prefixEnd_2875069 := by exact prefixLift 2875069
  have htrace : WordTrace (prefixWord ++ tailWord_2875069) baseStart_2875069 baseEnd_2875069 := by
    simpa [prefixWord, tailWord_2875069, baseEnd_2875069] using wordTrace_append hprefix tailTrace_2875069
  have hstable : (prefixWord ++ tailWord_2875069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875069).length < 2 ^ (prefixWord ++ tailWord_2875069).sum := by decide
  have hdescent : baseEnd_2875069 < baseStart_2875069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875080 : List Nat := [2, 1, 3, 1, 2, 2, 2, 2, 2, 5]
def baseStart_2875080 : Nat := 118140960795 + 2875080 * 2 ^ 59
def prefixEnd_2875080 : Nat := 4983230072969 + 3 ^ 40 * 2875080 * 2
def baseEnd_2875080 : Nat := 984198640085810979985169

theorem tailTrace_2875080 : CollatzResearch.WordTrace tailWord_2875080 prefixEnd_2875080 984198640085810979985169 := by
  unfold tailWord_2875080
  simp only [CollatzResearch.WordTrace]
  refine ⟨52431391212041829708323347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69908521616055772944431129 52431391212041829708323347)
  ·
    refine ⟨78647086818062744562485021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52431391212041829708323347 78647086818062744562485021)
    ·
      refine ⟨29492657556773529210931883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78647086818062744562485021 29492657556773529210931883)
      ·
        refine ⟨44238986335160293816397825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29492657556773529210931883 44238986335160293816397825)
        ·
          refine ⟨33179239751370220362298369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44238986335160293816397825 33179239751370220362298369)
          ·
            refine ⟨24884429813527665271723777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33179239751370220362298369 24884429813527665271723777)
            ·
              refine ⟨18663322360145748953792833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24884429813527665271723777 18663322360145748953792833)
              ·
                refine ⟨13997491770109311715344625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18663322360145748953792833 13997491770109311715344625)
                ·
                  refine ⟨10498118827581983786508469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13997491770109311715344625 10498118827581983786508469)
                  ·
                    refine ⟨984198640085810979985169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10498118827581983786508469 984198640085810979985169)
                    ·
                      rfl

theorem cell22_2875080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_2875080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2875080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2875080 prefixEnd_2875080 := by exact prefixLift 2875080
  have htrace : WordTrace (prefixWord ++ tailWord_2875080) baseStart_2875080 baseEnd_2875080 := by
    simpa [prefixWord, tailWord_2875080, baseEnd_2875080] using wordTrace_append hprefix tailTrace_2875080
  have hstable : (prefixWord ++ tailWord_2875080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875080).length < 2 ^ (prefixWord ++ tailWord_2875080).sum := by decide
  have hdescent : baseEnd_2875080 < baseStart_2875080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875095 : List Nat := [1, 1, 3, 2, 1, 3, 1, 1, 5, 4]
def baseStart_2875095 : Nat := 118140960795 + 2875095 * 2 ^ 59
def prefixEnd_2875095 : Nat := 4983230072969 + 3 ^ 40 * 2875095 * 2
def baseEnd_2875095 : Nat := 984203774892355940860123

theorem tailTrace_2875095 : CollatzResearch.WordTrace tailWord_2875095 prefixEnd_2875095 984203774892355940860123 := by
  unfold tailWord_2875095
  simp only [CollatzResearch.WordTrace]
  refine ⟨104863329519029316978442739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69908886346019544652295159 104863329519029316978442739)
  ·
    refine ⟨157294994278543975467664109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104863329519029316978442739 157294994278543975467664109)
    ·
      refine ⟨58985622854453990800374041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157294994278543975467664109 58985622854453990800374041)
      ·
        refine ⟨44239217140840493100280531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58985622854453990800374041 44239217140840493100280531)
        ·
          refine ⟨66358825711260739650420797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44239217140840493100280531 66358825711260739650420797)
          ·
            refine ⟨24884559641722777368907799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66358825711260739650420797 24884559641722777368907799)
            ·
              refine ⟨37326839462584166053361699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24884559641722777368907799 37326839462584166053361699)
              ·
                refine ⟨55990259193876249080042549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37326839462584166053361699 55990259193876249080042549)
                ·
                  refine ⟨5249086799425898351253989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55990259193876249080042549 5249086799425898351253989)
                  ·
                    refine ⟨984203774892355940860123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5249086799425898351253989 984203774892355940860123)
                    ·
                      rfl

theorem cell22_2875095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 5, 4].length) (baseStart_2875095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2875095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2875095 prefixEnd_2875095 := by exact prefixLift 2875095
  have htrace : WordTrace (prefixWord ++ tailWord_2875095) baseStart_2875095 baseEnd_2875095 := by
    simpa [prefixWord, tailWord_2875095, baseEnd_2875095] using wordTrace_append hprefix tailTrace_2875095
  have hstable : (prefixWord ++ tailWord_2875095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875095).length < 2 ^ (prefixWord ++ tailWord_2875095).sum := by decide
  have hdescent : baseEnd_2875095 < baseStart_2875095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875112 : List Nat := [2, 1, 4, 1, 3, 1, 2, 1, 3, 4]
def baseStart_2875112 : Nat := 118140960795 + 2875112 * 2 ^ 59
def prefixEnd_2875112 : Nat := 4983230072969 + 3 ^ 40 * 2875112 * 2
def baseEnd_2875112 : Nat := 984209594339773563185071

theorem tailTrace_2875112 : CollatzResearch.WordTrace tailWord_2875112 prefixEnd_2875112 984209594339773563185071 := by
  unfold tailWord_2875112
  simp only [CollatzResearch.WordTrace]
  refine ⟨52431974779983864440905795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69909299706645152587874393 52431974779983864440905795)
  ·
    refine ⟨78647962169975796661358693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52431974779983864440905795 78647962169975796661358693)
    ·
      refine ⟨14746492906870461874004755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78647962169975796661358693 14746492906870461874004755)
      ·
        refine ⟨22119739360305692811007133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14746492906870461874004755 22119739360305692811007133)
        ·
          refine ⟨8294902260114634804127675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22119739360305692811007133 8294902260114634804127675)
          ·
            refine ⟨12442353390171952206191513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8294902260114634804127675 12442353390171952206191513)
            ·
              refine ⟨9331765042628964154643635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12442353390171952206191513 9331765042628964154643635)
              ·
                refine ⟨13997647563943446231965453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9331765042628964154643635 13997647563943446231965453)
                ·
                  refine ⟨5249117836478792336987045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13997647563943446231965453 5249117836478792336987045)
                  ·
                    refine ⟨984209594339773563185071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5249117836478792336987045 984209594339773563185071)
                    ·
                      rfl

theorem cell22_2875112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_2875112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2875112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2875112 prefixEnd_2875112 := by exact prefixLift 2875112
  have htrace : WordTrace (prefixWord ++ tailWord_2875112) baseStart_2875112 baseEnd_2875112 := by
    simpa [prefixWord, tailWord_2875112, baseEnd_2875112] using wordTrace_append hprefix tailTrace_2875112
  have hstable : (prefixWord ++ tailWord_2875112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875112).length < 2 ^ (prefixWord ++ tailWord_2875112).sum := by decide
  have hdescent : baseEnd_2875112 < baseStart_2875112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875127 : List Nat := [1, 1, 3, 1, 1, 1, 5, 5, 4]
def baseStart_2875127 : Nat := 118140960795 + 2875127 * 2 ^ 59
def prefixEnd_2875127 : Nat := 4983230072969 + 3 ^ 40 * 2875127 * 2
def baseEnd_2875127 : Nat := 328071576382106174686675

theorem tailTrace_2875127 : CollatzResearch.WordTrace tailWord_2875127 prefixEnd_2875127 328071576382106174686675 := by
  unfold tailWord_2875127
  simp only [CollatzResearch.WordTrace]
  refine ⟨104864496654913386443607635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69909664436608924295738423 104864496654913386443607635)
  ·
    refine ⟨157296744982370079665411453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104864496654913386443607635 157296744982370079665411453)
    ·
      refine ⟨58986279368388779874529295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157296744982370079665411453 58986279368388779874529295)
      ·
        refine ⟨88479419052583169811793943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58986279368388779874529295 88479419052583169811793943)
        ·
          refine ⟨132719128578874754717690915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88479419052583169811793943 132719128578874754717690915)
          ·
            refine ⟨199078692868312132076536373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132719128578874754717690915 199078692868312132076536373)
            ·
              refine ⟨18663627456404262382175285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 199078692868312132076536373 18663627456404262382175285)
              ·
                refine ⟨1749715074037899598328933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18663627456404262382175285 1749715074037899598328933)
                ·
                  refine ⟨328071576382106174686675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1749715074037899598328933 328071576382106174686675)
                  ·
                    rfl

theorem cell22_2875127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 5, 4].length) (baseStart_2875127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2875127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2875127 prefixEnd_2875127 := by exact prefixLift 2875127
  have htrace : WordTrace (prefixWord ++ tailWord_2875127) baseStart_2875127 baseEnd_2875127 := by
    simpa [prefixWord, tailWord_2875127, baseEnd_2875127] using wordTrace_append hprefix tailTrace_2875127
  have hstable : (prefixWord ++ tailWord_2875127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875127).length < 2 ^ (prefixWord ++ tailWord_2875127).sum := by decide
  have hdescent : baseEnd_2875127 < baseStart_2875127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875159 : List Nat := [1, 1, 3, 4, 2, 3, 1, 1, 1, 5]
def baseStart_2875159 : Nat := 118140960795 + 2875159 * 2 ^ 59
def prefixEnd_2875159 : Nat := 4983230072969 + 3 ^ 40 * 2875159 * 2
def baseEnd_2875159 : Nat := 984225683400281107259927

theorem tailTrace_2875159 : CollatzResearch.WordTrace tailWord_2875159 prefixEnd_2875159 984225683400281107259927 := by
  unfold tailWord_2875159
  simp only [CollatzResearch.WordTrace]
  refine ⟨104865663790797455908772531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69910442527198303939181687 104865663790797455908772531)
  ·
    refine ⟨157298495686196183863158797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104865663790797455908772531 157298495686196183863158797)
    ·
      refine ⟨58986935882323568948684549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157298495686196183863158797 58986935882323568948684549)
      ·
        refine ⟨11060050477935669177878353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58986935882323568948684549 11060050477935669177878353)
        ·
          refine ⟨8295037858451751883408765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11060050477935669177878353 8295037858451751883408765)
          ·
            refine ⟨3110639196919406956278287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8295037858451751883408765 3110639196919406956278287)
            ·
              refine ⟨4665958795379110434417431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3110639196919406956278287 4665958795379110434417431)
              ·
                refine ⟨6998938193068665651626147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4665958795379110434417431 6998938193068665651626147)
                ·
                  refine ⟨10498407289602998477439221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6998938193068665651626147 10498407289602998477439221)
                  ·
                    refine ⟨984225683400281107259927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10498407289602998477439221 984225683400281107259927)
                    ·
                      rfl

theorem cell22_2875159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 5].length) (baseStart_2875159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2875159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2875159 prefixEnd_2875159 := by exact prefixLift 2875159
  have htrace : WordTrace (prefixWord ++ tailWord_2875159) baseStart_2875159 baseEnd_2875159 := by
    simpa [prefixWord, tailWord_2875159, baseEnd_2875159] using wordTrace_append hprefix tailTrace_2875159
  have hstable : (prefixWord ++ tailWord_2875159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875159).length < 2 ^ (prefixWord ++ tailWord_2875159).sum := by decide
  have hdescent : baseEnd_2875159 < baseStart_2875159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875172 : List Nat := [2, 3, 1, 3, 2, 2, 1, 8]
def baseStart_2875172 : Nat := 118140960795 + 2875172 * 2 ^ 59
def prefixEnd_2875172 : Nat := 4983230072969 + 3 ^ 40 * 2875172 * 2
def baseEnd_2875172 : Nat := 109358903729550378520543

theorem tailTrace_2875172 : CollatzResearch.WordTrace tailWord_2875172 prefixEnd_2875172 109358903729550378520543 := by
  unfold tailWord_2875172
  simp only [CollatzResearch.WordTrace]
  refine ⟨52433068969875179564497885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69910758626500239419330513 52433068969875179564497885)
  ·
    refine ⟨19662400863703192336686707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52433068969875179564497885 19662400863703192336686707)
    ·
      refine ⟨29493601295554788505030061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19662400863703192336686707 29493601295554788505030061)
      ·
        refine ⟨11060100485833045689386273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29493601295554788505030061 11060100485833045689386273)
        ·
          refine ⟨8295075364374784267039705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11060100485833045689386273 8295075364374784267039705)
          ·
            refine ⟨6221306523281088200279779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8295075364374784267039705 6221306523281088200279779)
            ·
              refine ⟨9331959784921632300419669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6221306523281088200279779 9331959784921632300419669)
              ·
                refine ⟨109358903729550378520543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9331959784921632300419669 109358903729550378520543)
                ·
                  rfl

theorem cell22_2875172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 8].length) (baseStart_2875172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2875172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2875172 prefixEnd_2875172 := by exact prefixLift 2875172
  have htrace : WordTrace (prefixWord ++ tailWord_2875172) baseStart_2875172 baseEnd_2875172 := by
    simpa [prefixWord, tailWord_2875172, baseEnd_2875172] using wordTrace_append hprefix tailTrace_2875172
  have hstable : (prefixWord ++ tailWord_2875172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875172).length < 2 ^ (prefixWord ++ tailWord_2875172).sum := by decide
  have hdescent : baseEnd_2875172 < baseStart_2875172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875189 : List Nat := [1, 3, 3, 1, 5, 1, 8]
def baseStart_2875189 : Nat := 118140960795 + 2875189 * 2 ^ 59
def prefixEnd_2875189 : Nat := 4983230072969 + 3 ^ 40 * 2875189 * 2
def baseEnd_2875189 : Nat := 36453183444939667741105

theorem tailTrace_2875189 : CollatzResearch.WordTrace tailWord_2875189 prefixEnd_2875189 36453183444939667741105 := by
  unfold tailWord_2875189
  simp only [CollatzResearch.WordTrace]
  refine ⟨104866757980688771032364621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69911171987125847354909747 104866757980688771032364621)
  ·
    refine ⟨39325034242758289137136733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104866757980688771032364621 39325034242758289137136733)
    ·
      refine ⟨14746887841034358426426275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39325034242758289137136733 14746887841034358426426275)
      ·
        refine ⟨22120331761551537639639413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14746887841034358426426275 22120331761551537639639413)
        ·
          refine ⟨2073781102645456653716195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22120331761551537639639413 2073781102645456653716195)
          ·
            refine ⟨3110671653968184980574293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2073781102645456653716195 3110671653968184980574293)
            ·
              refine ⟨36453183444939667741105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3110671653968184980574293 36453183444939667741105)
              ·
                rfl

theorem cell22_2875189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 8].length) (baseStart_2875189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2875189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2875189 prefixEnd_2875189 := by exact prefixLift 2875189
  have htrace : WordTrace (prefixWord ++ tailWord_2875189) baseStart_2875189 baseEnd_2875189 := by
    simpa [prefixWord, tailWord_2875189, baseEnd_2875189] using wordTrace_append hprefix tailTrace_2875189
  have hstable : (prefixWord ++ tailWord_2875189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875189).length < 2 ^ (prefixWord ++ tailWord_2875189).sum := by decide
  have hdescent : baseEnd_2875189 < baseStart_2875189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875206 : List Nat := [6, 1, 1, 2, 1, 2, 2, 7]
def baseStart_2875206 : Nat := 118140960795 + 2875206 * 2 ^ 59
def prefixEnd_2875206 : Nat := 4983230072969 + 3 ^ 40 * 2875206 * 2
def baseEnd_2875206 : Nat := 109360196940087627926087

theorem tailTrace_2875206 : CollatzResearch.WordTrace tailWord_2875206 prefixEnd_2875206 109360196940087627926087 := by
  unfold tailWord_2875206
  simp only [CollatzResearch.WordTrace]
  refine ⟨3277105563175849466741671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 69911585347751455290488981 3277105563175849466741671)
  ·
    refine ⟨4915658344763774200112507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3277105563175849466741671 4915658344763774200112507)
    ·
      refine ⟨7373487517145661300168761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4915658344763774200112507 7373487517145661300168761)
      ·
        refine ⟨5530115637859245975126571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7373487517145661300168761 5530115637859245975126571)
        ·
          refine ⟨8295173456788868962689857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5530115637859245975126571 8295173456788868962689857)
          ·
            refine ⟨6221380092591651722017393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8295173456788868962689857 6221380092591651722017393)
            ·
              refine ⟨4666035069443738791513045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6221380092591651722017393 4666035069443738791513045)
              ·
                refine ⟨109360196940087627926087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4666035069443738791513045 109360196940087627926087)
                ·
                  rfl

theorem cell22_2875206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_2875206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2875206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2875206 prefixEnd_2875206 := by exact prefixLift 2875206
  have htrace : WordTrace (prefixWord ++ tailWord_2875206) baseStart_2875206 baseEnd_2875206 := by
    simpa [prefixWord, tailWord_2875206, baseEnd_2875206] using wordTrace_append hprefix tailTrace_2875206
  have hstable : (prefixWord ++ tailWord_2875206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875206).length < 2 ^ (prefixWord ++ tailWord_2875206).sum := by decide
  have hdescent : baseEnd_2875206 < baseStart_2875206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875339 : List Nat := [1, 1, 1, 1, 3, 4, 1, 4, 3, 3]
def baseStart_2875339 : Nat := 118140960795 + 2875339 * 2 ^ 59
def prefixEnd_2875339 : Nat := 4983230072969 + 3 ^ 40 * 2875339 * 2
def baseEnd_2875339 : Nat := 984287301078820637759375

theorem tailTrace_2875339 : CollatzResearch.WordTrace tailWord_2875339 prefixEnd_2875339 984287301078820637759375 := by
  unfold tailWord_2875339
  simp only [CollatzResearch.WordTrace]
  refine ⟨104872228930145346650325071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69914819286763564433550047 104872228930145346650325071)
  ·
    refine ⟨157308343395218019975487607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104872228930145346650325071 157308343395218019975487607)
    ·
      refine ⟨235962515092827029963231411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157308343395218019975487607 235962515092827029963231411)
      ·
        refine ⟨353943772639240544944847117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235962515092827029963231411 353943772639240544944847117)
        ·
          refine ⟨132728914739715204354317669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 353943772639240544944847117 132728914739715204354317669)
          ·
            refine ⟨24886671513696600816434563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132728914739715204354317669 24886671513696600816434563)
            ·
              refine ⟨37330007270544901224651845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24886671513696600816434563 37330007270544901224651845)
              ·
                refine ⟨6999376363227168979622221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37330007270544901224651845 6999376363227168979622221)
                ·
                  refine ⟨2624766136210188367358333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6999376363227168979622221 2624766136210188367358333)
                  ·
                    refine ⟨984287301078820637759375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2624766136210188367358333 984287301078820637759375)
                    ·
                      rfl

theorem cell22_2875339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 3, 3].length) (baseStart_2875339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2875339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2875339 prefixEnd_2875339 := by exact prefixLift 2875339
  have htrace : WordTrace (prefixWord ++ tailWord_2875339) baseStart_2875339 baseEnd_2875339 := by
    simpa [prefixWord, tailWord_2875339, baseEnd_2875339] using wordTrace_append hprefix tailTrace_2875339
  have hstable : (prefixWord ++ tailWord_2875339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875339).length < 2 ^ (prefixWord ++ tailWord_2875339).sum := by decide
  have hdescent : baseEnd_2875339 < baseStart_2875339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875352 : List Nat := [2, 1, 2, 2, 2, 2, 1, 1, 9]
def baseStart_2875352 : Nat := 118140960795 + 2875352 * 2 ^ 59
def prefixEnd_2875352 : Nat := 4983230072969 + 3 ^ 40 * 2875352 * 2
def baseEnd_2875352 : Nat := 328097250414830979061445

theorem tailTrace_2875352 : CollatzResearch.WordTrace tailWord_2875352 prefixEnd_2875352 328097250414830979061445 := by
  unfold tailWord_2875352
  simp only [CollatzResearch.WordTrace]
  refine ⟨52436351539549124935274155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69915135386065499913698873 52436351539549124935274155)
  ·
    refine ⟨78654527309323687402911233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52436351539549124935274155 78654527309323687402911233)
    ·
      refine ⟨58990895481992765552183425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78654527309323687402911233 58990895481992765552183425)
      ·
        refine ⟨44243171611494574164137569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58990895481992765552183425 44243171611494574164137569)
        ·
          refine ⟨33182378708620930623103177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44243171611494574164137569 33182378708620930623103177)
          ·
            refine ⟨24886784031465697967327383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33182378708620930623103177 24886784031465697967327383)
            ·
              refine ⟨37330176047198546950991075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24886784031465697967327383 37330176047198546950991075)
              ·
                refine ⟨55995264070797820426486613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37330176047198546950991075 55995264070797820426486613)
                ·
                  refine ⟨328097250414830979061445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 55995264070797820426486613 328097250414830979061445)
                  ·
                    rfl

theorem cell22_2875352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 9].length) (baseStart_2875352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2875352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2875352 prefixEnd_2875352 := by exact prefixLift 2875352
  have htrace : WordTrace (prefixWord ++ tailWord_2875352) baseStart_2875352 baseEnd_2875352 := by
    simpa [prefixWord, tailWord_2875352, baseEnd_2875352] using wordTrace_append hprefix tailTrace_2875352
  have hstable : (prefixWord ++ tailWord_2875352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875352).length < 2 ^ (prefixWord ++ tailWord_2875352).sum := by decide
  have hdescent : baseEnd_2875352 < baseStart_2875352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875491 : List Nat := [1, 1, 1, 5, 1, 1, 3, 3, 3, 3]
def baseStart_2875491 : Nat := 118140960795 + 2875491 * 2 ^ 59
def prefixEnd_2875491 : Nat := 4983230072969 + 3 ^ 40 * 2875491 * 2
def baseEnd_2875491 : Nat := 984339333785142907958909

theorem tailTrace_2875491 : CollatzResearch.WordTrace tailWord_2875491 prefixEnd_2875491 984339333785142907958909 := by
  unfold tailWord_2875491
  simp only [CollatzResearch.WordTrace]
  refine ⟨104877772825594676609858327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69918515217063117739905551 104877772825594676609858327)
  ·
    refine ⟨157316659238392014914787491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104877772825594676609858327 157316659238392014914787491)
    ·
      refine ⟨235974988857588022372181237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157316659238392014914787491 235974988857588022372181237)
      ·
        refine ⟨22122655205398877097391991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 235974988857588022372181237 22122655205398877097391991)
        ·
          refine ⟨33183982808098315646087987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22122655205398877097391991 33183982808098315646087987)
          ·
            refine ⟨49775974212147473469131981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33183982808098315646087987 49775974212147473469131981)
            ·
              refine ⟨18665990329555302550924493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49775974212147473469131981 18665990329555302550924493)
              ·
                refine ⟨6999746373583238456596685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18665990329555302550924493 6999746373583238456596685)
                ·
                  refine ⟨2624904890093714421223757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6999746373583238456596685 2624904890093714421223757)
                  ·
                    refine ⟨984339333785142907958909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2624904890093714421223757 984339333785142907958909)
                    ·
                      rfl

theorem cell22_2875491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 3, 3].length) (baseStart_2875491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2875491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2875491 prefixEnd_2875491 := by exact prefixLift 2875491
  have htrace : WordTrace (prefixWord ++ tailWord_2875491) baseStart_2875491 baseEnd_2875491 := by
    simpa [prefixWord, tailWord_2875491, baseEnd_2875491] using wordTrace_append hprefix tailTrace_2875491
  have hstable : (prefixWord ++ tailWord_2875491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875491).length < 2 ^ (prefixWord ++ tailWord_2875491).sum := by decide
  have hdescent : baseEnd_2875491 < baseStart_2875491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875525 : List Nat := [1, 3, 1, 1, 5, 1, 3, 3, 1, 3]
def baseStart_2875525 : Nat := 118140960795 + 2875525 * 2 ^ 59
def prefixEnd_2875525 : Nat := 4983230072969 + 3 ^ 40 * 2875525 * 2
def baseEnd_2875525 : Nat := 984350972679978152608805

theorem tailTrace_2875525 : CollatzResearch.WordTrace tailWord_2875525 prefixEnd_2875525 984350972679978152608805 := by
  unfold tailWord_2875525
  simp only [CollatzResearch.WordTrace]
  refine ⟨104879012907471500416596029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69919341938314333611064019 104879012907471500416596029)
  ·
    refine ⟨39329629840301812656223511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104879012907471500416596029 39329629840301812656223511)
    ·
      refine ⟨58994444760452718984335267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39329629840301812656223511 58994444760452718984335267)
      ·
        refine ⟨88491667140679078476502901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58994444760452718984335267 88491667140679078476502901)
        ·
          refine ⟨8296093794438663607172147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88491667140679078476502901 8296093794438663607172147)
          ·
            refine ⟨12444140691657995410758221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8296093794438663607172147 12444140691657995410758221)
            ·
              refine ⟨4666552759371748279034333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12444140691657995410758221 4666552759371748279034333)
              ·
                refine ⟨1749957284764405604637875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4666552759371748279034333 1749957284764405604637875)
                ·
                  refine ⟨2624935927146608406956813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1749957284764405604637875 2624935927146608406956813)
                  ·
                    refine ⟨984350972679978152608805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2624935927146608406956813 984350972679978152608805)
                    ·
                      rfl

theorem cell22_2875525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 3, 1, 3].length) (baseStart_2875525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2875525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2875525 prefixEnd_2875525 := by exact prefixLift 2875525
  have htrace : WordTrace (prefixWord ++ tailWord_2875525) baseStart_2875525 baseEnd_2875525 := by
    simpa [prefixWord, tailWord_2875525, baseEnd_2875525] using wordTrace_append hprefix tailTrace_2875525
  have hstable : (prefixWord ++ tailWord_2875525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875525).length < 2 ^ (prefixWord ++ tailWord_2875525).sum := by decide
  have hdescent : baseEnd_2875525 < baseStart_2875525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875660 : List Nat := [2, 2, 1, 2, 2, 2, 1, 6, 1, 3]
def baseStart_2875660 : Nat := 118140960795 + 2875660 * 2 ^ 59
def prefixEnd_2875660 : Nat := 4983230072969 + 3 ^ 40 * 2875660 * 2
def baseEnd_2875660 : Nat := 984397185938882800483391

theorem tailTrace_2875660 : CollatzResearch.WordTrace tailWord_2875660 prefixEnd_2875660 984397185938882800483391 := by
  unfold tailWord_2875660
  simp only [CollatzResearch.WordTrace]
  refine ⟨52441968380991209236380217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69922624507988278981840289 52441968380991209236380217)
  ·
    refine ⟨39331476285743406927285163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52441968380991209236380217 39331476285743406927285163)
    ·
      refine ⟨58997214428615110390927745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39331476285743406927285163 58997214428615110390927745)
      ·
        refine ⟨44247910821461332793195809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58997214428615110390927745 44247910821461332793195809)
        ·
          refine ⟨33185933116095999594896857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44247910821461332793195809 33185933116095999594896857)
          ·
            refine ⟨24889449837071999696172643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33185933116095999594896857 24889449837071999696172643)
            ·
              refine ⟨37334174755607999544258965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24889449837071999696172643 37334174755607999544258965)
              ·
                refine ⟨1750039441669124978637139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37334174755607999544258965 1750039441669124978637139)
                ·
                  refine ⟨2625059162503687467955709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1750039441669124978637139 2625059162503687467955709)
                  ·
                    refine ⟨984397185938882800483391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2625059162503687467955709 984397185938882800483391)
                    ·
                      rfl

theorem cell22_2875660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 6, 1, 3].length) (baseStart_2875660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2875660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2875660 prefixEnd_2875660 := by exact prefixLift 2875660
  have htrace : WordTrace (prefixWord ++ tailWord_2875660) baseStart_2875660 baseEnd_2875660 := by
    simpa [prefixWord, tailWord_2875660, baseEnd_2875660] using wordTrace_append hprefix tailTrace_2875660
  have hstable : (prefixWord ++ tailWord_2875660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875660).length < 2 ^ (prefixWord ++ tailWord_2875660).sum := by decide
  have hdescent : baseEnd_2875660 < baseStart_2875660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875731 : List Nat := [1, 1, 1, 2, 1, 1, 4, 4, 1, 6]
def baseStart_2875731 : Nat := 118140960795 + 2875731 * 2 ^ 59
def prefixEnd_2875731 : Nat := 4983230072969 + 3 ^ 40 * 2875731 * 2
def baseEnd_2875731 : Nat := 984421490689862281958173

theorem tailTrace_2875731 : CollatzResearch.WordTrace tailWord_2875731 prefixEnd_2875731 984421490689862281958173 := by
  unfold tailWord_2875731
  simp only [CollatzResearch.WordTrace]
  refine ⟨104886526344725197598595047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69924350896483465065730031 104886526344725197598595047)
  ·
    refine ⟨157329789517087796397892571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104886526344725197598595047 157329789517087796397892571)
    ·
      refine ⟨235994684275631694596838857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157329789517087796397892571 235994684275631694596838857)
      ·
        refine ⟨176996013206723770947629143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235994684275631694596838857 176996013206723770947629143)
        ·
          refine ⟨265494019810085656421443715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176996013206723770947629143 265494019810085656421443715)
          ·
            refine ⟨398241029715128484632165573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265494019810085656421443715 398241029715128484632165573)
            ·
              refine ⟨74670193071586590868531045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 398241029715128484632165573 74670193071586590868531045)
              ·
                refine ⟨14000661200922485787849571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74670193071586590868531045 14000661200922485787849571)
                ·
                  refine ⟨21000991801383728681774357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14000661200922485787849571 21000991801383728681774357)
                  ·
                    refine ⟨984421490689862281958173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21000991801383728681774357 984421490689862281958173)
                    ·
                      rfl

theorem cell22_2875731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 6].length) (baseStart_2875731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2875731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2875731 prefixEnd_2875731 := by exact prefixLift 2875731
  have htrace : WordTrace (prefixWord ++ tailWord_2875731) baseStart_2875731 baseEnd_2875731 := by
    simpa [prefixWord, tailWord_2875731, baseEnd_2875731] using wordTrace_append hprefix tailTrace_2875731
  have hstable : (prefixWord ++ tailWord_2875731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875731).length < 2 ^ (prefixWord ++ tailWord_2875731).sum := by decide
  have hdescent : baseEnd_2875731 < baseStart_2875731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875765 : List Nat := [1, 3, 4, 1, 2, 1, 2, 2, 2, 4]
def baseStart_2875765 : Nat := 118140960795 + 2875765 * 2 ^ 59
def prefixEnd_2875765 : Nat := 4983230072969 + 3 ^ 40 * 2875765 * 2
def baseEnd_2875765 : Nat := 984433129584697526608069

theorem tailTrace_2875765 : CollatzResearch.WordTrace tailWord_2875765 prefixEnd_2875765 984433129584697526608069 := by
  unfold tailWord_2875765
  simp only [CollatzResearch.WordTrace]
  refine ⟨104887766426602021405332749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69925177617734680936888499 104887766426602021405332749)
  ·
    refine ⟨39332912409975758026999781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104887766426602021405332749 39332912409975758026999781)
    ·
      refine ⟨7374921076870454630062459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39332912409975758026999781 7374921076870454630062459)
      ·
        refine ⟨11062381615305681945093689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7374921076870454630062459 11062381615305681945093689)
        ·
          refine ⟨8296786211479261458820267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11062381615305681945093689 8296786211479261458820267)
          ·
            refine ⟨12445179317218892188230401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8296786211479261458820267 12445179317218892188230401)
            ·
              refine ⟨9333884487914169141172801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12445179317218892188230401 9333884487914169141172801)
              ·
                refine ⟨7000413365935626855879601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9333884487914169141172801 7000413365935626855879601)
                ·
                  refine ⟨5250310024451720141909701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7000413365935626855879601 5250310024451720141909701)
                  ·
                    refine ⟨984433129584697526608069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5250310024451720141909701 984433129584697526608069)
                    ·
                      rfl

theorem cell22_2875765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_2875765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2875765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2875765 prefixEnd_2875765 := by exact prefixLift 2875765
  have htrace : WordTrace (prefixWord ++ tailWord_2875765) baseStart_2875765 baseEnd_2875765 := by
    simpa [prefixWord, tailWord_2875765, baseEnd_2875765] using wordTrace_append hprefix tailTrace_2875765
  have hstable : (prefixWord ++ tailWord_2875765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875765).length < 2 ^ (prefixWord ++ tailWord_2875765).sum := by decide
  have hdescent : baseEnd_2875765 < baseStart_2875765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875812 : List Nat := [2, 3, 1, 2, 1, 1, 3, 5, 1, 3]
def baseStart_2875812 : Nat := 118140960795 + 2875812 * 2 ^ 59
def prefixEnd_2875812 : Nat := 4983230072969 + 3 ^ 40 * 2875812 * 2
def baseEnd_2875812 : Nat := 984449218645205070682925

theorem tailTrace_2875812 : CollatzResearch.WordTrace tailWord_2875812 prefixEnd_2875812 984449218645205070682925 := by
  unfold tailWord_2875812
  simp only [CollatzResearch.WordTrace]
  refine ⟨52444740328715874216146845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69926320438287832288195793 52444740328715874216146845)
  ·
    refine ⟨19666777623268452831055067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52444740328715874216146845 19666777623268452831055067)
    ·
      refine ⟨29500166434902679246582601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19666777623268452831055067 29500166434902679246582601)
      ·
        refine ⟨22125124826177009434936951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29500166434902679246582601 22125124826177009434936951)
        ·
          refine ⟨33187687239265514152405427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22125124826177009434936951 33187687239265514152405427)
          ·
            refine ⟨49781530858898271228608141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33187687239265514152405427 49781530858898271228608141)
            ·
              refine ⟨18668074072086851710728053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49781530858898271228608141 18668074072086851710728053)
              ·
                refine ⟨1750131944258142347880755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18668074072086851710728053 1750131944258142347880755)
                ·
                  refine ⟨2625197916387213521821133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1750131944258142347880755 2625197916387213521821133)
                  ·
                    refine ⟨984449218645205070682925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2625197916387213521821133 984449218645205070682925)
                    ·
                      rfl

theorem cell22_2875812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 5, 1, 3].length) (baseStart_2875812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2875812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2875812 prefixEnd_2875812 := by exact prefixLift 2875812
  have htrace : WordTrace (prefixWord ++ tailWord_2875812) baseStart_2875812 baseEnd_2875812 := by
    simpa [prefixWord, tailWord_2875812, baseEnd_2875812] using wordTrace_append hprefix tailTrace_2875812
  have hstable : (prefixWord ++ tailWord_2875812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875812).length < 2 ^ (prefixWord ++ tailWord_2875812).sum := by decide
  have hdescent : baseEnd_2875812 < baseStart_2875812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875818 : List Nat := [3, 1, 6, 1, 1, 2, 1, 2, 2, 3]
def baseStart_2875818 : Nat := 118140960795 + 2875818 * 2 ^ 59
def prefixEnd_2875818 : Nat := 4983230072969 + 3 ^ 40 * 2875818 * 2
def baseEnd_2875818 : Nat := 984451272567823055032907

theorem tailTrace_2875818 : CollatzResearch.WordTrace tailWord_2875818 prefixEnd_2875818 984451272567823055032907 := by
  unfold tailWord_2875818
  simp only [CollatzResearch.WordTrace]
  refine ⟨26222424873852502864253027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69926466330273340971341405 26222424873852502864253027)
  ·
    refine ⟨39333637310778754296379541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26222424873852502864253027 39333637310778754296379541)
    ·
      refine ⟨1843764248942754107642791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 39333637310778754296379541 1843764248942754107642791)
      ·
        refine ⟨2765646373414131161464187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1843764248942754107642791 2765646373414131161464187)
        ·
          refine ⟨4148469560121196742196281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2765646373414131161464187 4148469560121196742196281)
          ·
            refine ⟨3111352170090897556647211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4148469560121196742196281 3111352170090897556647211)
            ·
              refine ⟨4667028255136346334970817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3111352170090897556647211 4667028255136346334970817)
              ·
                refine ⟨3500271191352259751228113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4667028255136346334970817 3500271191352259751228113)
                ·
                  refine ⟨2625203393514194813421085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3500271191352259751228113 2625203393514194813421085)
                  ·
                    refine ⟨984451272567823055032907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2625203393514194813421085 984451272567823055032907)
                    ·
                      rfl

theorem cell22_2875818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_2875818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2875818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2875818 prefixEnd_2875818 := by exact prefixLift 2875818
  have htrace : WordTrace (prefixWord ++ tailWord_2875818) baseStart_2875818 baseEnd_2875818 := by
    simpa [prefixWord, tailWord_2875818, baseEnd_2875818] using wordTrace_append hprefix tailTrace_2875818
  have hstable : (prefixWord ++ tailWord_2875818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875818).length < 2 ^ (prefixWord ++ tailWord_2875818).sum := by decide
  have hdescent : baseEnd_2875818 < baseStart_2875818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875825 : List Nat := [1, 2, 2, 4, 1, 2, 3, 2, 5]
def baseStart_2875825 : Nat := 118140960795 + 2875825 * 2 ^ 59
def prefixEnd_2875825 : Nat := 4983230072969 + 3 ^ 40 * 2875825 * 2
def baseEnd_2875825 : Nat := 328151222936959123369295

theorem tailTrace_2875825 : CollatzResearch.WordTrace tailWord_2875825 prefixEnd_2875825 328151222936959123369295 := by
  unfold tailWord_2875825
  simp only [CollatzResearch.WordTrace]
  refine ⟨104889954806384651652516929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69926636537589767768344619 104889954806384651652516929)
  ·
    refine ⟨78667466104788488739387697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104889954806384651652516929 78667466104788488739387697)
    ·
      refine ⟨59000599578591366554540773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78667466104788488739387697 59000599578591366554540773)
      ·
        refine ⟨11062612420985881228976395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59000599578591366554540773 11062612420985881228976395)
        ·
          refine ⟨16593918631478821843464593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11062612420985881228976395 16593918631478821843464593)
          ·
            refine ⟨12445438973609116382598445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16593918631478821843464593 12445438973609116382598445)
            ·
              refine ⟨4667039615103418643474417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12445438973609116382598445 4667039615103418643474417)
              ·
                refine ⟨3500279711327563982605813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4667039615103418643474417 3500279711327563982605813)
                ·
                  refine ⟨328151222936959123369295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3500279711327563982605813 328151222936959123369295)
                  ·
                    rfl

theorem cell22_2875825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 2, 5].length) (baseStart_2875825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2875825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2875825 prefixEnd_2875825 := by exact prefixLift 2875825
  have htrace : WordTrace (prefixWord ++ tailWord_2875825) baseStart_2875825 baseEnd_2875825 := by
    simpa [prefixWord, tailWord_2875825, baseEnd_2875825] using wordTrace_append hprefix tailTrace_2875825
  have hstable : (prefixWord ++ tailWord_2875825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875825).length < 2 ^ (prefixWord ++ tailWord_2875825).sum := by decide
  have hdescent : baseEnd_2875825 < baseStart_2875825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875906 : List Nat := [3, 4, 1, 2, 2, 2, 1, 2, 1, 4]
def baseStart_2875906 : Nat := 118140960795 + 2875906 * 2 ^ 59
def prefixEnd_2875906 : Nat := 4983230072969 + 3 ^ 40 * 2875906 * 2
def baseEnd_2875906 : Nat := 984481396766220158832637

theorem tailTrace_2875906 : CollatzResearch.WordTrace tailWord_2875906 prefixEnd_2875906 984481396766220158832637 := by
  unfold tailWord_2875906
  simp only [CollatzResearch.WordTrace]
  refine ⟨26223227279772800621553893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69928606079394134990810381 26223227279772800621553893)
  ·
    refine ⟨4916855114957400116541355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26223227279772800621553893 4916855114957400116541355)
    ·
      refine ⟨7375282672436100174812033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4916855114957400116541355 7375282672436100174812033)
      ·
        refine ⟨5531462004327075131109025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7375282672436100174812033 5531462004327075131109025)
        ·
          refine ⟨4148596503245306348331769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5531462004327075131109025 4148596503245306348331769)
          ·
            refine ⟨3111447377433979761248827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4148596503245306348331769 3111447377433979761248827)
            ·
              refine ⟨4667171066150969641873241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3111447377433979761248827 4667171066150969641873241)
              ·
                refine ⟨3500378299613227231404931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4667171066150969641873241 3500378299613227231404931)
                ·
                  refine ⟨5250567449419840847107397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3500378299613227231404931 5250567449419840847107397)
                  ·
                    refine ⟨984481396766220158832637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5250567449419840847107397 984481396766220158832637)
                    ·
                      rfl

theorem cell22_2875906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_2875906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2875906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2875906 prefixEnd_2875906 := by exact prefixLift 2875906
  have htrace : WordTrace (prefixWord ++ tailWord_2875906) baseStart_2875906 baseEnd_2875906 := by
    simpa [prefixWord, tailWord_2875906, baseEnd_2875906] using wordTrace_append hprefix tailTrace_2875906
  have hstable : (prefixWord ++ tailWord_2875906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875906).length < 2 ^ (prefixWord ++ tailWord_2875906).sum := by decide
  have hdescent : baseEnd_2875906 < baseStart_2875906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875960 : List Nat := [2, 1, 2, 1, 4, 1, 1, 5, 5]
def baseStart_2875960 : Nat := 118140960795 + 2875960 * 2 ^ 59
def prefixEnd_2875960 : Nat := 4983230072969 + 3 ^ 40 * 2875960 * 2
def baseEnd_2875960 : Nat := 328166627356594005994157

theorem tailTrace_2875960 : CollatzResearch.WordTrace tailWord_2875960 prefixEnd_2875960 328166627356594005994157 := by
  unfold tailWord_2875960
  simp only [CollatzResearch.WordTrace]
  refine ⟨52447439330447784854340667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69929919107263713139120889 52447439330447784854340667)
  ·
    refine ⟨78671158995671677281511001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52447439330447784854340667 78671158995671677281511001)
    ·
      refine ⟨59003369246753757961133251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78671158995671677281511001 59003369246753757961133251)
      ·
        refine ⟨88505053870130636941699877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59003369246753757961133251 88505053870130636941699877)
        ·
          refine ⟨16594697600649494426568727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88505053870130636941699877 16594697600649494426568727)
          ·
            refine ⟨24892046400974241639853091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16594697600649494426568727 24892046400974241639853091)
            ·
              refine ⟨37338069601461362459779637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24892046400974241639853091 37338069601461362459779637)
              ·
                refine ⟨3500444025137002730604341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37338069601461362459779637 3500444025137002730604341)
                ·
                  refine ⟨328166627356594005994157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3500444025137002730604341 328166627356594005994157)
                  ·
                    rfl

theorem cell22_2875960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 5, 5].length) (baseStart_2875960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2875960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2875960 prefixEnd_2875960 := by exact prefixLift 2875960
  have htrace : WordTrace (prefixWord ++ tailWord_2875960) baseStart_2875960 baseEnd_2875960 := by
    simpa [prefixWord, tailWord_2875960, baseEnd_2875960] using wordTrace_append hprefix tailTrace_2875960
  have hstable : (prefixWord ++ tailWord_2875960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875960).length < 2 ^ (prefixWord ++ tailWord_2875960).sum := by decide
  have hdescent : baseEnd_2875960 < baseStart_2875960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2875981 : List Nat := [1, 6, 1, 1, 2, 1, 1, 5, 1, 3]
def baseStart_2875981 : Nat := 118140960795 + 2875981 * 2 ^ 59
def prefixEnd_2875981 : Nat := 4983230072969 + 3 ^ 40 * 2875981 * 2
def baseEnd_2875981 : Nat := 984507070798944963207407

theorem tailTrace_2875981 : CollatzResearch.WordTrace tailWord_2875981 prefixEnd_2875981 984507070798944963207407 := by
  unfold tailWord_2875981
  simp only [CollatzResearch.WordTrace]
  refine ⟨104895644593819490295195797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69930429729212993530130531 104895644593819490295195797)
  ·
    refine ⟨4916983340335288607587303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 104895644593819490295195797 4916983340335288607587303)
    ·
      refine ⟨7375475010502932911380955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4916983340335288607587303 7375475010502932911380955)
      ·
        refine ⟨11063212515754399367071433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7375475010502932911380955 11063212515754399367071433)
        ·
          refine ⟨8297409386815799525303575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11063212515754399367071433 8297409386815799525303575)
          ·
            refine ⟨12446114080223699287955363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8297409386815799525303575 12446114080223699287955363)
            ·
              refine ⟨18669171120335548931933045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12446114080223699287955363 18669171120335548931933045)
              ·
                refine ⟨1750234792531457712368723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18669171120335548931933045 1750234792531457712368723)
                ·
                  refine ⟨2625352188797186568553085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1750234792531457712368723 2625352188797186568553085)
                  ·
                    refine ⟨984507070798944963207407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2625352188797186568553085 984507070798944963207407)
                    ·
                      rfl

theorem cell22_2875981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_2875981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2875981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2875981 prefixEnd_2875981 := by exact prefixLift 2875981
  have htrace : WordTrace (prefixWord ++ tailWord_2875981) baseStart_2875981 baseEnd_2875981 := by
    simpa [prefixWord, tailWord_2875981, baseEnd_2875981] using wordTrace_append hprefix tailTrace_2875981
  have hstable : (prefixWord ++ tailWord_2875981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2875981).length < 2 ^ (prefixWord ++ tailWord_2875981).sum := by decide
  have hdescent : baseEnd_2875981 < baseStart_2875981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2875981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876035 : List Nat := [1, 1, 1, 3, 3, 1, 4, 1, 1, 6]
def baseStart_2876035 : Nat := 118140960795 + 2876035 * 2 ^ 59
def prefixEnd_2876035 : Nat := 4983230072969 + 3 ^ 40 * 2876035 * 2
def baseEnd_2876035 : Nat := 984525556102506822357241

theorem tailTrace_2876035 : CollatzResearch.WordTrace tailWord_2876035 prefixEnd_2876035 984525556102506822357241 := by
  unfold tailWord_2876035
  simp only [CollatzResearch.WordTrace]
  refine ⟨104897614135623857517661559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69931742757082571678441039 104897614135623857517661559)
  ·
    refine ⟨157346421203435786276492339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104897614135623857517661559 157346421203435786276492339)
    ·
      refine ⟨236019631805153679414738509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157346421203435786276492339 236019631805153679414738509)
      ·
        refine ⟨88507361926932629780526941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236019631805153679414738509 88507361926932629780526941)
        ·
          refine ⟨33190260722599736167697603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88507361926932629780526941 33190260722599736167697603)
          ·
            refine ⟨49785391083899604251546405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33190260722599736167697603 49785391083899604251546405)
            ·
              refine ⟨9334760828231175797164951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49785391083899604251546405 9334760828231175797164951)
              ·
                refine ⟨14002141242346763695747427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9334760828231175797164951 14002141242346763695747427)
                ·
                  refine ⟨21003211863520145543621141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14002141242346763695747427 21003211863520145543621141)
                  ·
                    refine ⟨984525556102506822357241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21003211863520145543621141 984525556102506822357241)
                    ·
                      rfl

theorem cell22_2876035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 6].length) (baseStart_2876035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2876035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2876035 prefixEnd_2876035 := by exact prefixLift 2876035
  have htrace : WordTrace (prefixWord ++ tailWord_2876035) baseStart_2876035 baseEnd_2876035 := by
    simpa [prefixWord, tailWord_2876035, baseEnd_2876035] using wordTrace_append hprefix tailTrace_2876035
  have hstable : (prefixWord ++ tailWord_2876035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876035).length < 2 ^ (prefixWord ++ tailWord_2876035).sum := by decide
  have hdescent : baseEnd_2876035 < baseStart_2876035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876037 : List Nat := [1, 3, 1, 1, 4, 2, 1, 2, 4, 3]
def baseStart_2876037 : Nat := 118140960795 + 2876037 * 2 ^ 59
def prefixEnd_2876037 : Nat := 4983230072969 + 3 ^ 40 * 2876037 * 2
def baseEnd_2876037 : Nat := 984526240743379483807235

theorem tailTrace_2876037 : CollatzResearch.WordTrace tailWord_2876037 prefixEnd_2876037 984526240743379483807235 := by
  unfold tailWord_2876037
  simp only [CollatzResearch.WordTrace]
  refine ⟨104897687081616611859234365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69931791387744407906156243 104897687081616611859234365)
  ·
    refine ⟨39336632655606229447212887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104897687081616611859234365 39336632655606229447212887)
    ·
      refine ⟨59004948983409344170819331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39336632655606229447212887 59004948983409344170819331)
      ·
        refine ⟨88507423475114016256228997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59004948983409344170819331 88507423475114016256228997)
        ·
          refine ⟨16595141901583878048042937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88507423475114016256228997 16595141901583878048042937)
          ·
            refine ⟨12446356426187908536032203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16595141901583878048042937 12446356426187908536032203)
            ·
              refine ⟨18669534639281862804048305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12446356426187908536032203 18669534639281862804048305)
              ·
                refine ⟨14002150979461397103036229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18669534639281862804048305 14002150979461397103036229)
                ·
                  refine ⟨2625403308649011956819293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14002150979461397103036229 2625403308649011956819293)
                  ·
                    refine ⟨984526240743379483807235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2625403308649011956819293 984526240743379483807235)
                    ·
                      rfl

theorem cell22_2876037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 4, 3].length) (baseStart_2876037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2876037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2876037 prefixEnd_2876037 := by exact prefixLift 2876037
  have htrace : WordTrace (prefixWord ++ tailWord_2876037) baseStart_2876037 baseEnd_2876037 := by
    simpa [prefixWord, tailWord_2876037, baseEnd_2876037] using wordTrace_append hprefix tailTrace_2876037
  have hstable : (prefixWord ++ tailWord_2876037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876037).length < 2 ^ (prefixWord ++ tailWord_2876037).sum := by decide
  have hdescent : baseEnd_2876037 < baseStart_2876037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876082 : List Nat := [3, 2, 1, 1, 1, 2, 1, 3, 5, 3]
def baseStart_2876082 : Nat := 118140960795 + 2876082 * 2 ^ 59
def prefixEnd_2876082 : Nat := 4983230072969 + 3 ^ 40 * 2876082 * 2
def baseEnd_2876082 : Nat := 984541645163014366432097

theorem tailTrace_2876082 : CollatzResearch.WordTrace tailWord_2876082 prefixEnd_2876082 984541645163014366432097 := by
  unfold tailWord_2876082
  simp only [CollatzResearch.WordTrace]
  refine ⟨26224832091613396136155625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69932885577635723029748333 26224832091613396136155625)
  ·
    refine ⟨19668624068710047102116719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26224832091613396136155625 19668624068710047102116719)
    ·
      refine ⟨29502936103065070653175079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19668624068710047102116719 29502936103065070653175079)
      ·
        refine ⟨44254404154597605979762619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29502936103065070653175079 44254404154597605979762619)
        ·
          refine ⟨66381606231896408969643929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44254404154597605979762619 66381606231896408969643929)
          ·
            refine ⟨49786204673922306727232947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66381606231896408969643929 49786204673922306727232947)
            ·
              refine ⟨74679307010883460090849421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49786204673922306727232947 74679307010883460090849421)
              ·
                refine ⟨28004740129081297534068533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74679307010883460090849421 28004740129081297534068533)
                ·
                  refine ⟨2625444387101371643818925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28004740129081297534068533 2625444387101371643818925)
                  ·
                    refine ⟨984541645163014366432097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2625444387101371643818925 984541645163014366432097)
                    ·
                      rfl

theorem cell22_2876082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 5, 3].length) (baseStart_2876082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2876082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2876082 prefixEnd_2876082 := by exact prefixLift 2876082
  have htrace : WordTrace (prefixWord ++ tailWord_2876082) baseStart_2876082 baseEnd_2876082 := by
    simpa [prefixWord, tailWord_2876082, baseEnd_2876082] using wordTrace_append hprefix tailTrace_2876082
  have hstable : (prefixWord ++ tailWord_2876082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876082).length < 2 ^ (prefixWord ++ tailWord_2876082).sum := by decide
  have hdescent : baseEnd_2876082 < baseStart_2876082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876127 : List Nat := [1, 1, 2, 3, 2, 4, 1, 1, 2, 5]
def baseStart_2876127 : Nat := 118140960795 + 2876127 * 2 ^ 59
def prefixEnd_2876127 : Nat := 4983230072969 + 3 ^ 40 * 2876127 * 2
def baseEnd_2876127 : Nat := 984557049582649249056959

theorem tailTrace_2876127 : CollatzResearch.WordTrace tailWord_2876127 prefixEnd_2876127 984557049582649249056959 := by
  unfold tailWord_2876127
  simp only [CollatzResearch.WordTrace]
  refine ⟨104900969651290557230010635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69933979767527038153340423 104900969651290557230010635)
  ·
    refine ⟨157351454476935835845015953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104900969651290557230010635 157351454476935835845015953)
    ·
      refine ⟨118013590857701876883761965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157351454476935835845015953 118013590857701876883761965)
      ·
        refine ⟨44255096571638203831410737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118013590857701876883761965 44255096571638203831410737)
        ·
          refine ⟨33191322428728652873558053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44255096571638203831410737 33191322428728652873558053)
          ·
            refine ⟨6223372955386622413792135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33191322428728652873558053 6223372955386622413792135)
            ·
              refine ⟨9335059433079933620688203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6223372955386622413792135 9335059433079933620688203)
              ·
                refine ⟨14002589149619900431032305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9335059433079933620688203 14002589149619900431032305)
                ·
                  refine ⟨10501941862214925323274229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14002589149619900431032305 10501941862214925323274229)
                  ·
                    refine ⟨984557049582649249056959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10501941862214925323274229 984557049582649249056959)
                    ·
                      rfl

theorem cell22_2876127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 5].length) (baseStart_2876127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2876127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2876127 prefixEnd_2876127 := by exact prefixLift 2876127
  have htrace : WordTrace (prefixWord ++ tailWord_2876127) baseStart_2876127 baseEnd_2876127 := by
    simpa [prefixWord, tailWord_2876127, baseEnd_2876127] using wordTrace_append hprefix tailTrace_2876127
  have hstable : (prefixWord ++ tailWord_2876127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876127).length < 2 ^ (prefixWord ++ tailWord_2876127).sum := by decide
  have hdescent : baseEnd_2876127 < baseStart_2876127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876155 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 2, 9]
def baseStart_2876155 : Nat := 118140960795 + 2876155 * 2 ^ 59
def prefixEnd_2876155 : Nat := 4983230072969 + 3 ^ 40 * 2876155 * 2
def baseEnd_2876155 : Nat := 984566634554866509356873

theorem tailTrace_2876155 : CollatzResearch.WordTrace tailWord_2876155 prefixEnd_2876155 984566634554866509356873 := by
  unfold tailWord_2876155
  simp only [CollatzResearch.WordTrace]
  refine ⟨104901990895189118012029919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69934660596792745341353279 104901990895189118012029919)
  ·
    refine ⟨157352986342783677018044879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104901990895189118012029919 157352986342783677018044879)
    ·
      refine ⟨236029479514175515527067319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157352986342783677018044879 236029479514175515527067319)
      ·
        refine ⟨354044219271263273290600979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236029479514175515527067319 354044219271263273290600979)
        ·
          refine ⟨531066328906894909935901469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354044219271263273290600979 531066328906894909935901469)
          ·
            refine ⟨199149873340085591225963051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 531066328906894909935901469 199149873340085591225963051)
            ·
              refine ⟨298724810010128386838944577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199149873340085591225963051 298724810010128386838944577)
              ·
                refine ⟨224043607507596290129208433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 298724810010128386838944577 224043607507596290129208433)
                ·
                  refine ⟨168032705630697217596906325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 224043607507596290129208433 168032705630697217596906325)
                  ·
                    refine ⟨984566634554866509356873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 168032705630697217596906325 984566634554866509356873)
                    ·
                      rfl

theorem cell22_2876155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 9].length) (baseStart_2876155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2876155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2876155 prefixEnd_2876155 := by exact prefixLift 2876155
  have htrace : WordTrace (prefixWord ++ tailWord_2876155) baseStart_2876155 baseEnd_2876155 := by
    simpa [prefixWord, tailWord_2876155, baseEnd_2876155] using wordTrace_append hprefix tailTrace_2876155
  have hstable : (prefixWord ++ tailWord_2876155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876155).length < 2 ^ (prefixWord ++ tailWord_2876155).sum := by decide
  have hdescent : baseEnd_2876155 < baseStart_2876155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876206 : List Nat := [4, 1, 3, 2, 1, 1, 1, 2, 4, 3]
def baseStart_2876206 : Nat := 118140960795 + 2876206 * 2 ^ 59
def prefixEnd_2876206 : Nat := 4983230072969 + 3 ^ 40 * 2876206 * 2
def baseEnd_2876206 : Nat := 984584092897119376331717

theorem tailTrace_2876206 : CollatzResearch.WordTrace tailWord_2876206 prefixEnd_2876206 984584092897119376331717 := by
  unfold tailWord_2876206
  simp only [CollatzResearch.WordTrace]
  refine ⟨13112981377250544215267059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69935900678669569148090981 13112981377250544215267059)
  ·
    refine ⟨19669472065875816322900589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13112981377250544215267059 19669472065875816322900589)
    ·
      refine ⟨7376052024703431121087721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19669472065875816322900589 7376052024703431121087721)
      ·
        refine ⟨5532039018527573340815791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7376052024703431121087721 5532039018527573340815791)
        ·
          refine ⟨8298058527791360011223687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5532039018527573340815791 8298058527791360011223687)
          ·
            refine ⟨12447087791687040016835531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8298058527791360011223687 12447087791687040016835531)
            ·
              refine ⟨18670631687530560025253297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12447087791687040016835531 18670631687530560025253297)
              ·
                refine ⟨14002973765647920018939973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18670631687530560025253297 14002973765647920018939973)
                ·
                  refine ⟨2625557581058985003551245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14002973765647920018939973 2625557581058985003551245)
                  ·
                    refine ⟨984584092897119376331717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2625557581058985003551245 984584092897119376331717)
                    ·
                      rfl

theorem cell22_2876206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_2876206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2876206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2876206 prefixEnd_2876206 := by exact prefixLift 2876206
  have htrace : WordTrace (prefixWord ++ tailWord_2876206) baseStart_2876206 baseEnd_2876206 := by
    simpa [prefixWord, tailWord_2876206, baseEnd_2876206] using wordTrace_append hprefix tailTrace_2876206
  have hstable : (prefixWord ++ tailWord_2876206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876206).length < 2 ^ (prefixWord ++ tailWord_2876206).sum := by decide
  have hdescent : baseEnd_2876206 < baseStart_2876206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876221 : List Nat := [1, 4, 1, 4, 2, 1, 1, 2, 2, 4]
def baseStart_2876221 : Nat := 118140960795 + 2876221 * 2 ^ 59
def prefixEnd_2876221 : Nat := 4983230072969 + 3 ^ 40 * 2876221 * 2
def baseEnd_2876221 : Nat := 984589227703664337206671

theorem tailTrace_2876221 : CollatzResearch.WordTrace tailWord_2876221 prefixEnd_2876221 984589227703664337206671 := by
  unfold tailWord_2876221
  simp only [CollatzResearch.WordTrace]
  refine ⟨104904398112950011283932517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69936265408633340855955011 104904398112950011283932517)
  ·
    refine ⟨19669574646178127115737347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104904398112950011283932517 19669574646178127115737347)
    ·
      refine ⟨29504361969267190673606021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19669574646178127115737347 29504361969267190673606021)
      ·
        refine ⟨5532067869237598251301129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29504361969267190673606021 5532067869237598251301129)
        ·
          refine ⟨4149050901928198688475847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5532067869237598251301129 4149050901928198688475847)
          ·
            refine ⟨6223576352892298032713771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4149050901928198688475847 6223576352892298032713771)
            ·
              refine ⟨9335364529338447049070657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6223576352892298032713771 9335364529338447049070657)
              ·
                refine ⟨7001523397003835286802993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9335364529338447049070657 7001523397003835286802993)
                ·
                  refine ⟨5251142547752876465102245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7001523397003835286802993 5251142547752876465102245)
                  ·
                    refine ⟨984589227703664337206671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5251142547752876465102245 984589227703664337206671)
                    ·
                      rfl

theorem cell22_2876221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_2876221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2876221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2876221 prefixEnd_2876221 := by exact prefixLift 2876221
  have htrace : WordTrace (prefixWord ++ tailWord_2876221) baseStart_2876221 baseEnd_2876221 := by
    simpa [prefixWord, tailWord_2876221, baseEnd_2876221] using wordTrace_append hprefix tailTrace_2876221
  have hstable : (prefixWord ++ tailWord_2876221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876221).length < 2 ^ (prefixWord ++ tailWord_2876221).sum := by decide
  have hdescent : baseEnd_2876221 < baseStart_2876221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876225 : List Nat := [1, 2, 5, 3, 1, 1, 3, 2, 4]
def baseStart_2876225 : Nat := 118140960795 + 2876225 * 2 ^ 59
def prefixEnd_2876225 : Nat := 4983230072969 + 3 ^ 40 * 2876225 * 2
def baseEnd_2876225 : Nat := 328196865661803220035553

theorem tailTrace_2876225 : CollatzResearch.WordTrace tailWord_2876225 prefixEnd_2876225 328196865661803220035553 := by
  unfold tailWord_2876225
  simp only [CollatzResearch.WordTrace]
  refine ⟨104904544004935519967078129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69936362669957013311385419 104904544004935519967078129)
  ·
    refine ⟨78678408003701639975308597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104904544004935519967078129 78678408003701639975308597)
    ·
      refine ⟨7376100750347028747685181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78678408003701639975308597 7376100750347028747685181)
      ·
        refine ⟨2766037781380135780381943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7376100750347028747685181 2766037781380135780381943)
        ·
          refine ⟨4149056672070203670572915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2766037781380135780381943 4149056672070203670572915)
          ·
            refine ⟨6223585008105305505859373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4149056672070203670572915 6223585008105305505859373)
            ·
              refine ⟨2333844378039489564697265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6223585008105305505859373 2333844378039489564697265)
              ·
                refine ⟨1750383283529617173522949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2333844378039489564697265 1750383283529617173522949)
                ·
                  refine ⟨328196865661803220035553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1750383283529617173522949 328196865661803220035553)
                  ·
                    rfl

theorem cell22_2876225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 2, 4].length) (baseStart_2876225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2876225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2876225 prefixEnd_2876225 := by exact prefixLift 2876225
  have htrace : WordTrace (prefixWord ++ tailWord_2876225) baseStart_2876225 baseEnd_2876225 := by
    simpa [prefixWord, tailWord_2876225, baseEnd_2876225] using wordTrace_append hprefix tailTrace_2876225
  have hstable : (prefixWord ++ tailWord_2876225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876225).length < 2 ^ (prefixWord ++ tailWord_2876225).sum := by decide
  have hdescent : baseEnd_2876225 < baseStart_2876225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876232 : List Nat := [2, 1, 3, 1, 1, 3, 2, 1, 2, 6]
def baseStart_2876232 : Nat := 118140960795 + 2876232 * 2 ^ 59
def prefixEnd_2876232 : Nat := 4983230072969 + 3 ^ 40 * 2876232 * 2
def baseEnd_2876232 : Nat := 984592993228463975181637

theorem tailTrace_2876232 : CollatzResearch.WordTrace tailWord_2876232 prefixEnd_2876232 984592993228463975181637 := by
  unfold tailWord_2876232
  simp only [CollatzResearch.WordTrace]
  refine ⟨52452399657955080081291475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69936532877273440108388633 52452399657955080081291475)
  ·
    refine ⟨78678599486932620121937213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52452399657955080081291475 78678599486932620121937213)
    ·
      refine ⟨29504474807599732545726455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78678599486932620121937213 29504474807599732545726455)
      ·
        refine ⟨44256712211399598818589683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29504474807599732545726455 44256712211399598818589683)
        ·
          refine ⟨66385068317099398227884525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44256712211399598818589683 66385068317099398227884525)
          ·
            refine ⟨24894400618912274335456697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66385068317099398227884525 24894400618912274335456697)
            ·
              refine ⟨18670800464184205751592523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24894400618912274335456697 18670800464184205751592523)
              ·
                refine ⟨28006200696276308627388785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18670800464184205751592523 28006200696276308627388785)
                ·
                  refine ⟨21004650522207231470541589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28006200696276308627388785 21004650522207231470541589)
                  ·
                    refine ⟨984592993228463975181637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21004650522207231470541589 984592993228463975181637)
                    ·
                      rfl

theorem cell22_2876232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_2876232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2876232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2876232 prefixEnd_2876232 := by exact prefixLift 2876232
  have htrace : WordTrace (prefixWord ++ tailWord_2876232) baseStart_2876232 baseEnd_2876232 := by
    simpa [prefixWord, tailWord_2876232, baseEnd_2876232] using wordTrace_append hprefix tailTrace_2876232
  have hstable : (prefixWord ++ tailWord_2876232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876232).length < 2 ^ (prefixWord ++ tailWord_2876232).sum := by decide
  have hdescent : baseEnd_2876232 < baseStart_2876232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876234 : List Nat := [3, 1, 2, 1, 1, 1, 2, 5, 3, 3]
def baseStart_2876234 : Nat := 118140960795 + 2876234 * 2 ^ 59
def prefixEnd_2876234 : Nat := 4983230072969 + 3 ^ 40 * 2876234 * 2
def baseEnd_2876234 : Nat := 984593677869336636631631

theorem tailTrace_2876234 : CollatzResearch.WordTrace tailWord_2876234 prefixEnd_2876234 984593677869336636631631 := by
  unfold tailWord_2876234
  simp only [CollatzResearch.WordTrace]
  refine ⟨26226218065475728626038939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69936581507935276336103837 26226218065475728626038939)
  ·
    refine ⟨39339327098213592939058409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26226218065475728626038939 39339327098213592939058409)
    ·
      refine ⟨29504495323660194704293807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39339327098213592939058409 29504495323660194704293807)
      ·
        refine ⟨44256742985490292056440711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29504495323660194704293807 44256742985490292056440711)
        ·
          refine ⟨66385114478235438084661067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44256742985490292056440711 66385114478235438084661067)
          ·
            refine ⟨99577671717353157126991601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66385114478235438084661067 99577671717353157126991601)
            ·
              refine ⟨74683253788014867845243701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99577671717353157126991601 74683253788014867845243701)
              ·
                refine ⟨7001555042626393860491597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74683253788014867845243701 7001555042626393860491597)
                ·
                  refine ⟨2625583140984897697684349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7001555042626393860491597 2625583140984897697684349)
                  ·
                    refine ⟨984593677869336636631631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2625583140984897697684349 984593677869336636631631)
                    ·
                      rfl

theorem cell22_2876234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 3, 3].length) (baseStart_2876234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2876234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2876234 prefixEnd_2876234 := by exact prefixLift 2876234
  have htrace : WordTrace (prefixWord ++ tailWord_2876234) baseStart_2876234 baseEnd_2876234 := by
    simpa [prefixWord, tailWord_2876234, baseEnd_2876234] using wordTrace_append hprefix tailTrace_2876234
  have hstable : (prefixWord ++ tailWord_2876234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876234).length < 2 ^ (prefixWord ++ tailWord_2876234).sum := by decide
  have hdescent : baseEnd_2876234 < baseStart_2876234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876309 : List Nat := [1, 3, 2, 1, 1, 5, 1, 2, 6]
def baseStart_2876309 : Nat := 118140960795 + 2876309 * 2 ^ 59
def prefixEnd_2876309 : Nat := 4983230072969 + 3 ^ 40 * 2876309 * 2
def baseEnd_2876309 : Nat := 328206450634020480335467

theorem tailTrace_2876309 : CollatzResearch.WordTrace tailWord_2876309 prefixEnd_2876309 328206450634020480335467 := by
  unfold tailWord_2876309
  simp only [CollatzResearch.WordTrace]
  refine ⟨104907607736631202313135981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69938405157754134875423987 104907607736631202313135981)
  ·
    refine ⟨39340352901236700867425993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104907607736631202313135981 39340352901236700867425993)
    ·
      refine ⟨29505264675927525650569495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39340352901236700867425993 29505264675927525650569495)
      ·
        refine ⟨44257897013891288475854243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29505264675927525650569495 44257897013891288475854243)
        ·
          refine ⟨66386845520836932713781365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44257897013891288475854243 66386845520836932713781365)
          ·
            refine ⟨6223766767578462441917003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66386845520836932713781365 6223766767578462441917003)
            ·
              refine ⟨9335650151367693662875505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6223766767578462441917003 9335650151367693662875505)
              ·
                refine ⟨7001737613525770247156629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9335650151367693662875505 7001737613525770247156629)
                ·
                  refine ⟨328206450634020480335467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7001737613525770247156629 328206450634020480335467)
                  ·
                    rfl

theorem cell22_2876309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 6].length) (baseStart_2876309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2876309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2876309 prefixEnd_2876309 := by exact prefixLift 2876309
  have htrace : WordTrace (prefixWord ++ tailWord_2876309) baseStart_2876309 baseEnd_2876309 := by
    simpa [prefixWord, tailWord_2876309, baseEnd_2876309] using wordTrace_append hprefix tailTrace_2876309
  have hstable : (prefixWord ++ tailWord_2876309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876309).length < 2 ^ (prefixWord ++ tailWord_2876309).sum := by decide
  have hdescent : baseEnd_2876309 < baseStart_2876309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876324 : List Nat := [2, 3, 1, 2, 1, 2, 1, 4, 1, 5]
def baseStart_2876324 : Nat := 118140960795 + 2876324 * 2 ^ 59
def prefixEnd_2876324 : Nat := 4983230072969 + 3 ^ 40 * 2876324 * 2
def baseEnd_2876324 : Nat := 984624486708606401881355

theorem tailTrace_2876324 : CollatzResearch.WordTrace tailWord_2876324 prefixEnd_2876324 984624486708606401881355 := by
  unfold tailWord_2876324
  simp only [CollatzResearch.WordTrace]
  refine ⟨52454077415788429937466013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69938769887717906583288017 52454077415788429937466013)
  ·
    refine ⟨19670279030920661226549755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52454077415788429937466013 19670279030920661226549755)
    ·
      refine ⟨29505418546380991839824633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19670279030920661226549755 29505418546380991839824633)
      ·
        refine ⟨22129063909785743879868475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29505418546380991839824633 22129063909785743879868475)
        ·
          refine ⟨33193595864678615819802713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22129063909785743879868475 33193595864678615819802713)
          ·
            refine ⟨24895196898508961864852035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33193595864678615819802713 24895196898508961864852035)
            ·
              refine ⟨37342795347763442797278053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24895196898508961864852035 37342795347763442797278053)
              ·
                refine ⟨7001774127705645524489635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37342795347763442797278053 7001774127705645524489635)
                ·
                  refine ⟨10502661191558468286734453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7001774127705645524489635 10502661191558468286734453)
                  ·
                    refine ⟨984624486708606401881355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10502661191558468286734453 984624486708606401881355)
                    ·
                      rfl

theorem cell22_2876324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_2876324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2876324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2876324 prefixEnd_2876324 := by exact prefixLift 2876324
  have htrace : WordTrace (prefixWord ++ tailWord_2876324) baseStart_2876324 baseEnd_2876324 := by
    simpa [prefixWord, tailWord_2876324, baseEnd_2876324] using wordTrace_append hprefix tailTrace_2876324
  have hstable : (prefixWord ++ tailWord_2876324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876324).length < 2 ^ (prefixWord ++ tailWord_2876324).sum := by decide
  have hdescent : baseEnd_2876324 < baseStart_2876324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876341 : List Nat := [1, 3, 3, 2, 1, 1, 3, 1, 4, 3]
def baseStart_2876341 : Nat := 118140960795 + 2876341 * 2 ^ 59
def prefixEnd_2876341 : Nat := 4983230072969 + 3 ^ 40 * 2876341 * 2
def baseEnd_2876341 : Nat := 984630306156024024206303

theorem tailTrace_2876341 : CollatzResearch.WordTrace tailWord_2876341 prefixEnd_2876341 984630306156024024206303 := by
  unfold tailWord_2876341
  simp only [CollatzResearch.WordTrace]
  refine ⟨104908774872515271778300877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69939183248343514518867251 104908774872515271778300877)
  ·
    refine ⟨39340790577193226916862829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104908774872515271778300877 39340790577193226916862829)
    ·
      refine ⟨14752796466447460093823561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39340790577193226916862829 14752796466447460093823561)
      ·
        refine ⟨11064597349835595070367671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14752796466447460093823561 11064597349835595070367671)
        ·
          refine ⟨16596896024753392605551507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11064597349835595070367671 16596896024753392605551507)
          ·
            refine ⟨24895344037130088908327261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16596896024753392605551507 24895344037130088908327261)
            ·
              refine ⟨9335754013923783340622723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24895344037130088908327261 9335754013923783340622723)
              ·
                refine ⟨14003631020885675010934085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9335754013923783340622723 14003631020885675010934085)
                ·
                  refine ⟨2625680816416064064550141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14003631020885675010934085 2625680816416064064550141)
                  ·
                    refine ⟨984630306156024024206303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2625680816416064064550141 984630306156024024206303)
                    ·
                      rfl

theorem cell22_2876341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_2876341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2876341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2876341 prefixEnd_2876341 := by exact prefixLift 2876341
  have htrace : WordTrace (prefixWord ++ tailWord_2876341) baseStart_2876341 baseEnd_2876341 := by
    simpa [prefixWord, tailWord_2876341, baseEnd_2876341] using wordTrace_append hprefix tailTrace_2876341
  have hstable : (prefixWord ++ tailWord_2876341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876341).length < 2 ^ (prefixWord ++ tailWord_2876341).sum := by decide
  have hdescent : baseEnd_2876341 < baseStart_2876341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876399 : List Nat := [1, 1, 2, 1, 4, 3, 2, 1, 7]
def baseStart_2876399 : Nat := 118140960795 + 2876399 * 2 ^ 59
def prefixEnd_2876399 : Nat := 4983230072969 + 3 ^ 40 * 2876399 * 2
def baseEnd_2876399 : Nat := 328216720247110402085375

theorem tailTrace_2876399 : CollatzResearch.WordTrace tailWord_2876399 prefixEnd_2876399 328216720247110402085375 := by
  unfold tailWord_2876399
  simp only [CollatzResearch.WordTrace]
  refine ⟨104910890306305147683912251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69940593537536765122608167 104910890306305147683912251)
  ·
    refine ⟨157366335459457721525868377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104910890306305147683912251 157366335459457721525868377)
    ·
      refine ⟨118024751594593291144401283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157366335459457721525868377 118024751594593291144401283)
      ·
        refine ⟨177037127391889936716601925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118024751594593291144401283 177037127391889936716601925)
        ·
          refine ⟨33194461385979363134362861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 177037127391889936716601925 33194461385979363134362861)
          ·
            refine ⟨12447923019742261175386073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33194461385979363134362861 12447923019742261175386073)
            ·
              refine ⟨9335942264806695881539555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12447923019742261175386073 9335942264806695881539555)
              ·
                refine ⟨14003913397210043822309333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9335942264806695881539555 14003913397210043822309333)
                ·
                  refine ⟨328216720247110402085375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14003913397210043822309333 328216720247110402085375)
                  ·
                    rfl

theorem cell22_2876399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 7].length) (baseStart_2876399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2876399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2876399 prefixEnd_2876399 := by exact prefixLift 2876399
  have htrace : WordTrace (prefixWord ++ tailWord_2876399) baseStart_2876399 baseEnd_2876399 := by
    simpa [prefixWord, tailWord_2876399, baseEnd_2876399] using wordTrace_append hprefix tailTrace_2876399
  have hstable : (prefixWord ++ tailWord_2876399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876399).length < 2 ^ (prefixWord ++ tailWord_2876399).sum := by decide
  have hdescent : baseEnd_2876399 < baseStart_2876399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876459 : List Nat := [1, 1, 1, 1, 2, 1, 5, 2, 3, 5]
def baseStart_2876459 : Nat := 118140960795 + 2876459 * 2 ^ 59
def prefixEnd_2876459 : Nat := 4983230072969 + 3 ^ 40 * 2876459 * 2
def baseEnd_2876459 : Nat := 984670699967511049755941

theorem tailTrace_2876459 : CollatzResearch.WordTrace tailWord_2876459 prefixEnd_2876459 984670699967511049755941 := by
  unfold tailWord_2876459
  simp only [CollatzResearch.WordTrace]
  refine ⟨104913078686087777931096431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69942052457391851954064287 104913078686087777931096431)
  ·
    refine ⟨157369618029131666896644647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104913078686087777931096431 157369618029131666896644647)
    ·
      refine ⟨236054427043697500344966971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157369618029131666896644647 236054427043697500344966971)
      ·
        refine ⟨354081640565546250517450457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236054427043697500344966971 354081640565546250517450457)
        ·
          refine ⟨265561230424159687888087843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 354081640565546250517450457 265561230424159687888087843)
          ·
            refine ⟨398341845636239531832131765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265561230424159687888087843 398341845636239531832131765)
            ·
              refine ⟨37344548028397456109262353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 398341845636239531832131765 37344548028397456109262353)
              ·
                refine ⟨28008411021298092081946765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37344548028397456109262353 28008411021298092081946765)
                ·
                  refine ⟨10503154132986784530730037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28008411021298092081946765 10503154132986784530730037)
                  ·
                    refine ⟨984670699967511049755941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10503154132986784530730037 984670699967511049755941)
                    ·
                      rfl

theorem cell22_2876459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 5].length) (baseStart_2876459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2876459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2876459 prefixEnd_2876459 := by exact prefixLift 2876459
  have htrace : WordTrace (prefixWord ++ tailWord_2876459) baseStart_2876459 baseEnd_2876459 := by
    simpa [prefixWord, tailWord_2876459, baseEnd_2876459] using wordTrace_append hprefix tailTrace_2876459
  have hstable : (prefixWord ++ tailWord_2876459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876459).length < 2 ^ (prefixWord ++ tailWord_2876459).sum := by decide
  have hdescent : baseEnd_2876459 < baseStart_2876459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876476 : List Nat := [2, 2, 2, 2, 2, 2, 1, 3, 1, 5]
def baseStart_2876476 : Nat := 118140960795 + 2876476 * 2 ^ 59
def prefixEnd_2876476 : Nat := 4983230072969 + 3 ^ 40 * 2876476 * 2
def baseEnd_2876476 : Nat := 984676519414928672080889

theorem tailTrace_2876476 : CollatzResearch.WordTrace tailWord_2876476 prefixEnd_2876476 984676519414928672080889 := by
  unfold tailWord_2876476
  simp only [CollatzResearch.WordTrace]
  refine ⟨52456849363513094917232641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69942465818017459889643521 52456849363513094917232641)
  ·
    refine ⟨39342637022634821187924481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52456849363513094917232641 39342637022634821187924481)
    ·
      refine ⟨29506977766976115890943361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39342637022634821187924481 29506977766976115890943361)
      ·
        refine ⟨22130233325232086918207521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29506977766976115890943361 22130233325232086918207521)
        ·
          refine ⟨16597674993924065188655641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22130233325232086918207521 16597674993924065188655641)
          ·
            refine ⟨12448256245443048891491731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16597674993924065188655641 12448256245443048891491731)
            ·
              refine ⟨18672384368164573337237597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12448256245443048891491731 18672384368164573337237597)
              ·
                refine ⟨7002144138061715001464099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18672384368164573337237597 7002144138061715001464099)
                ·
                  refine ⟨10503216207092572502196149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7002144138061715001464099 10503216207092572502196149)
                  ·
                    refine ⟨984676519414928672080889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10503216207092572502196149 984676519414928672080889)
                    ·
                      rfl

theorem cell22_2876476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_2876476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2876476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2876476 prefixEnd_2876476 := by exact prefixLift 2876476
  have htrace : WordTrace (prefixWord ++ tailWord_2876476) baseStart_2876476 baseEnd_2876476 := by
    simpa [prefixWord, tailWord_2876476, baseEnd_2876476] using wordTrace_append hprefix tailTrace_2876476
  have hstable : (prefixWord ++ tailWord_2876476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876476).length < 2 ^ (prefixWord ++ tailWord_2876476).sum := by decide
  have hdescent : baseEnd_2876476 < baseStart_2876476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876478 : List Nat := [4, 2, 1, 3, 1, 2, 1, 2, 6]
def baseStart_2876478 : Nat := 118140960795 + 2876478 * 2 ^ 59
def prefixEnd_2876478 : Nat := 4983230072969 + 3 ^ 40 * 2876478 * 2
def baseEnd_2876478 : Nat := 328225734685267111176961

theorem tailTrace_2876478 : CollatzResearch.WordTrace tailWord_2876478 prefixEnd_2876478 328225734685267111176961 := by
  unfold tailWord_2876478
  simp only [CollatzResearch.WordTrace]
  refine ⟨13114221459127368022004761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69942514448679296117358725 13114221459127368022004761)
  ·
    refine ⟨9835666094345526016503571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13114221459127368022004761 9835666094345526016503571)
    ·
      refine ⟨14753499141518289024755357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9835666094345526016503571 14753499141518289024755357)
      ·
        refine ⟨5532562178069358384283259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14753499141518289024755357 5532562178069358384283259)
        ·
          refine ⟨8298843267104037576424889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5532562178069358384283259 8298843267104037576424889)
          ·
            refine ⟨6224132450328028182318667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8298843267104037576424889 6224132450328028182318667)
            ·
              refine ⟨9336198675492042273478001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6224132450328028182318667 9336198675492042273478001)
              ·
                refine ⟨7002149006619031705108501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9336198675492042273478001 7002149006619031705108501)
                ·
                  refine ⟨328225734685267111176961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7002149006619031705108501 328225734685267111176961)
                  ·
                    rfl

theorem cell22_2876478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_2876478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2876478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2876478 prefixEnd_2876478 := by exact prefixLift 2876478
  have htrace : WordTrace (prefixWord ++ tailWord_2876478) baseStart_2876478 baseEnd_2876478 := by
    simpa [prefixWord, tailWord_2876478, baseEnd_2876478] using wordTrace_append hprefix tailTrace_2876478
  have hstable : (prefixWord ++ tailWord_2876478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876478).length < 2 ^ (prefixWord ++ tailWord_2876478).sum := by decide
  have hdescent : baseEnd_2876478 < baseStart_2876478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876493 : List Nat := [1, 6, 1, 1, 1, 2, 2, 2, 1, 5]
def baseStart_2876493 : Nat := 118140960795 + 2876493 * 2 ^ 59
def prefixEnd_2876493 : Nat := 4983230072969 + 3 ^ 40 * 2876493 * 2
def baseEnd_2876493 : Nat := 984682338862346294405837

theorem tailTrace_2876493 : CollatzResearch.WordTrace tailWord_2876493 prefixEnd_2876493 984682338862346294405837 := by
  unfold tailWord_2876493
  simp only [CollatzResearch.WordTrace]
  refine ⟨104914318767964601737834133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69942879178643067825222755 104914318767964601737834133)
  ·
    refine ⟨4917858692248340706460975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 104914318767964601737834133 4917858692248340706460975)
    ·
      refine ⟨7376788038372511059691463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4917858692248340706460975 7376788038372511059691463)
      ·
        refine ⟨11065182057558766589537195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7376788038372511059691463 11065182057558766589537195)
        ·
          refine ⟨16597773086338149884305793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11065182057558766589537195 16597773086338149884305793)
          ·
            refine ⟨12448329814753612413229345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16597773086338149884305793 12448329814753612413229345)
            ·
              refine ⟨9336247361065209309922009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12448329814753612413229345 9336247361065209309922009)
              ·
                refine ⟨7002185520798906982441507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9336247361065209309922009 7002185520798906982441507)
                ·
                  refine ⟨10503278281198360473662261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7002185520798906982441507 10503278281198360473662261)
                  ·
                    refine ⟨984682338862346294405837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10503278281198360473662261 984682338862346294405837)
                    ·
                      rfl

theorem cell22_2876493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_2876493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2876493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2876493 prefixEnd_2876493 := by exact prefixLift 2876493
  have htrace : WordTrace (prefixWord ++ tailWord_2876493) baseStart_2876493 baseEnd_2876493 := by
    simpa [prefixWord, tailWord_2876493, baseEnd_2876493] using wordTrace_append hprefix tailTrace_2876493
  have hstable : (prefixWord ++ tailWord_2876493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876493).length < 2 ^ (prefixWord ++ tailWord_2876493).sum := by decide
  have hdescent : baseEnd_2876493 < baseStart_2876493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876613 : List Nat := [1, 3, 1, 1, 1, 1, 3, 7, 4]
def baseStart_2876613 : Nat := 118140960795 + 2876613 * 2 ^ 59
def prefixEnd_2876613 : Nat := 4983230072969 + 3 ^ 40 * 2876613 * 2
def baseEnd_2876613 : Nat := 328241139104901993801823

theorem tailTrace_2876613 : CollatzResearch.WordTrace tailWord_2876613 prefixEnd_2876613 328241139104901993801823 := by
  unfold tailWord_2876613
  simp only [CollatzResearch.WordTrace]
  refine ⟨104918695527529862232202493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69945797018353241488134995 104918695527529862232202493)
  ·
    refine ⟨39344510822823698337075935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104918695527529862232202493 39344510822823698337075935)
    ·
      refine ⟨59016766234235547505613903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39344510822823698337075935 59016766234235547505613903)
      ·
        refine ⟨88525149351353321258420855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59016766234235547505613903 88525149351353321258420855)
        ·
          refine ⟨132787724027029981887631283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88525149351353321258420855 132787724027029981887631283)
          ·
            refine ⟨199181586040544972831446925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132787724027029981887631283 199181586040544972831446925)
            ·
              refine ⟨74693094765204364811792597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199181586040544972831446925 74693094765204364811792597)
              ·
                refine ⟨1750619408559477300276389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 74693094765204364811792597 1750619408559477300276389)
                ·
                  refine ⟨328241139104901993801823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1750619408559477300276389 328241139104901993801823)
                  ·
                    rfl

theorem cell22_2876613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 7, 4].length) (baseStart_2876613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2876613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2876613 prefixEnd_2876613 := by exact prefixLift 2876613
  have htrace : WordTrace (prefixWord ++ tailWord_2876613) baseStart_2876613 baseEnd_2876613 := by
    simpa [prefixWord, tailWord_2876613, baseEnd_2876613] using wordTrace_append hprefix tailTrace_2876613
  have hstable : (prefixWord ++ tailWord_2876613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876613).length < 2 ^ (prefixWord ++ tailWord_2876613).sum := by decide
  have hdescent : baseEnd_2876613 < baseStart_2876613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876645 : List Nat := [1, 3, 1, 4, 3, 1, 2, 1, 1, 5]
def baseStart_2876645 : Nat := 118140960795 + 2876645 * 2 ^ 59
def prefixEnd_2876645 : Nat := 4983230072969 + 3 ^ 40 * 2876645 * 2
def baseEnd_2876645 : Nat := 984734371568668564605371

theorem tailTrace_2876645 : CollatzResearch.WordTrace tailWord_2876645 prefixEnd_2876645 984734371568668564605371 := by
  unfold tailWord_2876645
  simp only [CollatzResearch.WordTrace]
  refine ⟨104919862663413931697367389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69946575108942621131578259 104919862663413931697367389)
  ·
    refine ⟨39344948498780224386512771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104919862663413931697367389 39344948498780224386512771)
    ·
      refine ⟨59017422748170336579769157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39344948498780224386512771 59017422748170336579769157)
      ·
        refine ⟨11065766765281938108706717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59017422748170336579769157 11065766765281938108706717)
        ·
          refine ⟨4149662536980726790765019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11065766765281938108706717 4149662536980726790765019)
          ·
            refine ⟨6224493805471090186147529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4149662536980726790765019 6224493805471090186147529)
            ·
              refine ⟨4668370354103317639610647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6224493805471090186147529 4668370354103317639610647)
              ·
                refine ⟨7002555531154976459415971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4668370354103317639610647 7002555531154976459415971)
                ·
                  refine ⟨10503833296732464689123957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7002555531154976459415971 10503833296732464689123957)
                  ·
                    refine ⟨984734371568668564605371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10503833296732464689123957 984734371568668564605371)
                    ·
                      rfl

theorem cell22_2876645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 5].length) (baseStart_2876645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2876645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2876645 prefixEnd_2876645 := by exact prefixLift 2876645
  have htrace : WordTrace (prefixWord ++ tailWord_2876645) baseStart_2876645 baseEnd_2876645 := by
    simpa [prefixWord, tailWord_2876645, baseEnd_2876645] using wordTrace_append hprefix tailTrace_2876645
  have hstable : (prefixWord ++ tailWord_2876645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876645).length < 2 ^ (prefixWord ++ tailWord_2876645).sum := by decide
  have hdescent : baseEnd_2876645 < baseStart_2876645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876780 : List Nat := [2, 2, 1, 1, 5, 2, 1, 2, 1, 5]
def baseStart_2876780 : Nat := 118140960795 + 2876780 * 2 ^ 59
def prefixEnd_2876780 : Nat := 4983230072969 + 3 ^ 40 * 2876780 * 2
def baseEnd_2876780 : Nat := 984780584827573212479957

theorem tailTrace_2876780 : CollatzResearch.WordTrace tailWord_2876780 prefixEnd_2876780 984780584827573212479957 := by
  unfold tailWord_2876780
  simp only [CollatzResearch.WordTrace]
  refine ⟨52462393258962424876765897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69949857678616566502354529 52462393258962424876765897)
  ·
    refine ⟨39346794944221818657574423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52462393258962424876765897 39346794944221818657574423)
    ·
      refine ⟨59020192416332727986361635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39346794944221818657574423 59020192416332727986361635)
      ·
        refine ⟨88530288624499091979542453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59020192416332727986361635 88530288624499091979542453)
        ·
          refine ⟨8299714558546789873082105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88530288624499091979542453 8299714558546789873082105)
          ·
            refine ⟨6224785918910092404811579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8299714558546789873082105 6224785918910092404811579)
            ·
              refine ⟨9337178878365138607217369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6224785918910092404811579 9337178878365138607217369)
              ·
                refine ⟨7002884158773853955413027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9337178878365138607217369 7002884158773853955413027)
                ·
                  refine ⟨10504326238160780933119541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7002884158773853955413027 10504326238160780933119541)
                  ·
                    refine ⟨984780584827573212479957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10504326238160780933119541 984780584827573212479957)
                    ·
                      rfl

theorem cell22_2876780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 5].length) (baseStart_2876780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2876780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2876780 prefixEnd_2876780 := by exact prefixLift 2876780
  have htrace : WordTrace (prefixWord ++ tailWord_2876780) baseStart_2876780 baseEnd_2876780 := by
    simpa [prefixWord, tailWord_2876780, baseEnd_2876780] using wordTrace_append hprefix tailTrace_2876780
  have hstable : (prefixWord ++ tailWord_2876780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876780).length < 2 ^ (prefixWord ++ tailWord_2876780).sum := by decide
  have hdescent : baseEnd_2876780 < baseStart_2876780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876797 : List Nat := [1, 4, 1, 1, 2, 2, 4, 2, 2, 3]
def baseStart_2876797 : Nat := 118140960795 + 2876797 * 2 ^ 59
def prefixEnd_2876797 : Nat := 4983230072969 + 3 ^ 40 * 2876797 * 2
def baseEnd_2876797 : Nat := 984786404274990834804905

theorem tailTrace_2876797 : CollatzResearch.WordTrace tailWord_2876797 prefixEnd_2876797 984786404274990834804905 := by
  unfold tailWord_2876797
  simp only [CollatzResearch.WordTrace]
  refine ⟨104925406558863261656900645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69950271039242174437933763 104925406558863261656900645)
  ·
    refine ⟨19673513729786861560668871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104925406558863261656900645 19673513729786861560668871)
    ·
      refine ⟨29510270594680292341003307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19673513729786861560668871 29510270594680292341003307)
      ·
        refine ⟨44265405892020438511504961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29510270594680292341003307 44265405892020438511504961)
        ·
          refine ⟨33199054419015328883628721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44265405892020438511504961 33199054419015328883628721)
          ·
            refine ⟨24899290814261496662721541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33199054419015328883628721 24899290814261496662721541)
            ·
              refine ⟨4668617027674030624260289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24899290814261496662721541 4668617027674030624260289)
              ·
                refine ⟨3501462770755522968195217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4668617027674030624260289 3501462770755522968195217)
                ·
                  refine ⟨2626097078066642226146413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3501462770755522968195217 2626097078066642226146413)
                  ·
                    refine ⟨984786404274990834804905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2626097078066642226146413 984786404274990834804905)
                    ·
                      rfl

theorem cell22_2876797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 2, 2, 3].length) (baseStart_2876797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2876797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2876797 prefixEnd_2876797 := by exact prefixLift 2876797
  have htrace : WordTrace (prefixWord ++ tailWord_2876797) baseStart_2876797 baseEnd_2876797 := by
    simpa [prefixWord, tailWord_2876797, baseEnd_2876797] using wordTrace_append hprefix tailTrace_2876797
  have hstable : (prefixWord ++ tailWord_2876797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876797).length < 2 ^ (prefixWord ++ tailWord_2876797).sum := by decide
  have hdescent : baseEnd_2876797 < baseStart_2876797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876823 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 4, 6]
def baseStart_2876823 : Nat := 118140960795 + 2876823 * 2 ^ 59
def prefixEnd_2876823 : Nat := 4983230072969 + 3 ^ 40 * 2876823 * 2
def baseEnd_2876823 : Nat := 984795304606335433654825

theorem tailTrace_2876823 : CollatzResearch.WordTrace tailWord_2876823 prefixEnd_2876823 984795304606335433654825 := by
  unfold tailWord_2876823
  simp only [CollatzResearch.WordTrace]
  refine ⟨104926354856769068097347123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69950903237846045398231415 104926354856769068097347123)
  ·
    refine ⟨157389532285153602146020685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104926354856769068097347123 157389532285153602146020685)
    ·
      refine ⟨59021074606932600804757757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157389532285153602146020685 59021074606932600804757757)
      ·
        refine ⟨22132902977599725301784159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59021074606932600804757757 22132902977599725301784159)
        ·
          refine ⟨33199354466399587952676239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22132902977599725301784159 33199354466399587952676239)
          ·
            refine ⟨49799031699599381929014359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33199354466399587952676239 49799031699599381929014359)
            ·
              refine ⟨74698547549399072893521539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49799031699599381929014359 74698547549399072893521539)
              ·
                refine ⟨112047821324098609340282309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74698547549399072893521539 112047821324098609340282309)
                ·
                  refine ⟨21008966498268489251302933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112047821324098609340282309 21008966498268489251302933)
                  ·
                    refine ⟨984795304606335433654825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21008966498268489251302933 984795304606335433654825)
                    ·
                      rfl

theorem cell22_2876823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 6].length) (baseStart_2876823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2876823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2876823 prefixEnd_2876823 := by exact prefixLift 2876823
  have htrace : WordTrace (prefixWord ++ tailWord_2876823) baseStart_2876823 baseEnd_2876823 := by
    simpa [prefixWord, tailWord_2876823, baseEnd_2876823] using wordTrace_append hprefix tailTrace_2876823
  have hstable : (prefixWord ++ tailWord_2876823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876823).length < 2 ^ (prefixWord ++ tailWord_2876823).sum := by decide
  have hdescent : baseEnd_2876823 < baseStart_2876823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876825 : List Nat := [1, 2, 1, 2, 1, 5, 1, 1, 5, 3]
def baseStart_2876825 : Nat := 118140960795 + 2876825 * 2 ^ 59
def prefixEnd_2876825 : Nat := 4983230072969 + 3 ^ 40 * 2876825 * 2
def baseEnd_2876825 : Nat := 984795989247208095104819

theorem tailTrace_2876825 : CollatzResearch.WordTrace tailWord_2876825 prefixEnd_2876825 984795989247208095104819 := by
  unfold tailWord_2876825
  simp only [CollatzResearch.WordTrace]
  refine ⟨104926427802761822438919929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69950951868507881625946619 104926427802761822438919929)
  ·
    refine ⟨78694820852071366829189947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104926427802761822438919929 78694820852071366829189947)
    ·
      refine ⟨118042231278107050243784921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78694820852071366829189947 118042231278107050243784921)
      ·
        refine ⟨88531673458580287682838691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118042231278107050243784921 88531673458580287682838691)
        ·
          refine ⟨132797510187870431524258037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88531673458580287682838691 132797510187870431524258037)
          ·
            refine ⟨12449766580112852955399191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 132797510187870431524258037 12449766580112852955399191)
            ·
              refine ⟨18674649870169279433098787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12449766580112852955399191 18674649870169279433098787)
              ·
                refine ⟨28011974805253919149648181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18674649870169279433098787 28011974805253919149648181)
                ·
                  refine ⟨2626122637992554920279517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28011974805253919149648181 2626122637992554920279517)
                  ·
                    refine ⟨984795989247208095104819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2626122637992554920279517 984795989247208095104819)
                    ·
                      rfl

theorem cell22_2876825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 5, 3].length) (baseStart_2876825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2876825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2876825 prefixEnd_2876825 := by exact prefixLift 2876825
  have htrace : WordTrace (prefixWord ++ tailWord_2876825) baseStart_2876825 baseEnd_2876825 := by
    simpa [prefixWord, tailWord_2876825, baseEnd_2876825] using wordTrace_append hprefix tailTrace_2876825
  have hstable : (prefixWord ++ tailWord_2876825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876825).length < 2 ^ (prefixWord ++ tailWord_2876825).sum := by decide
  have hdescent : baseEnd_2876825 < baseStart_2876825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876872 : List Nat := [2, 1, 3, 1, 3, 1, 5, 1, 5]
def baseStart_2876872 : Nat := 118140960795 + 2876872 * 2 ^ 59
def prefixEnd_2876872 : Nat := 4983230072969 + 3 ^ 40 * 2876872 * 2
def baseEnd_2876872 : Nat := 328270692769238546393225

theorem tailTrace_2876872 : CollatzResearch.WordTrace tailWord_2876872 prefixEnd_2876872 328270692769238546393225 := by
  unfold tailWord_2876872
  simp only [CollatzResearch.WordTrace]
  refine ⟨52464071016795774732940435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69952094689061032977253913 52464071016795774732940435)
  ·
    refine ⟨78696106525193662099410653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52464071016795774732940435 78696106525193662099410653)
    ·
      refine ⟨29511039946947623287278995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78696106525193662099410653 29511039946947623287278995)
      ·
        refine ⟨44266559920421434930918493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29511039946947623287278995 44266559920421434930918493)
        ·
          refine ⟨16599959970158038099094435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44266559920421434930918493 16599959970158038099094435)
          ·
            refine ⟨24899939955237057148641653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16599959970158038099094435 24899939955237057148641653)
            ·
              refine ⟨2334369370803474107685155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24899939955237057148641653 2334369370803474107685155)
              ·
                refine ⟨3501554056205211161527733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2334369370803474107685155 3501554056205211161527733)
                ·
                  refine ⟨328270692769238546393225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3501554056205211161527733 328270692769238546393225)
                  ·
                    rfl

theorem cell22_2876872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 1, 5].length) (baseStart_2876872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2876872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2876872 prefixEnd_2876872 := by exact prefixLift 2876872
  have htrace : WordTrace (prefixWord ++ tailWord_2876872) baseStart_2876872 baseEnd_2876872 := by
    simpa [prefixWord, tailWord_2876872, baseEnd_2876872] using wordTrace_append hprefix tailTrace_2876872
  have hstable : (prefixWord ++ tailWord_2876872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876872).length < 2 ^ (prefixWord ++ tailWord_2876872).sum := by decide
  have hdescent : baseEnd_2876872 < baseStart_2876872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876947 : List Nat := [1, 1, 1, 2, 1, 7, 2, 1, 2, 4]
def baseStart_2876947 : Nat := 118140960795 + 2876947 * 2 ^ 59
def prefixEnd_2876947 : Nat := 4983230072969 + 3 ^ 40 * 2876947 * 2
def baseEnd_2876947 : Nat := 984837752340440443554445

theorem tailTrace_2876947 : CollatzResearch.WordTrace tailWord_2876947 prefixEnd_2876947 984837752340440443554445 := by
  unfold tailWord_2876947
  simp only [CollatzResearch.WordTrace]
  refine ⟨104930877508319837274861095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69953918338879891516574063 104930877508319837274861095)
  ·
    refine ⟨157396316262479755912291643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104930877508319837274861095 157396316262479755912291643)
    ·
      refine ⟨236094474393719633868437465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157396316262479755912291643 236094474393719633868437465)
      ·
        refine ⟨177070855795289725401328099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236094474393719633868437465 177070855795289725401328099)
        ·
          refine ⟨265606283692934588101992149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177070855795289725401328099 265606283692934588101992149)
          ·
            refine ⟨6225147274053154408640441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 265606283692934588101992149 6225147274053154408640441)
            ·
              refine ⟨4668860455539865806480331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6225147274053154408640441 4668860455539865806480331)
              ·
                refine ⟨7003290683309798709720497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4668860455539865806480331 7003290683309798709720497)
                ·
                  refine ⟨5252468012482349032290373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7003290683309798709720497 5252468012482349032290373)
                  ·
                    refine ⟨984837752340440443554445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5252468012482349032290373 984837752340440443554445)
                    ·
                      rfl

theorem cell22_2876947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 2, 4].length) (baseStart_2876947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2876947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2876947 prefixEnd_2876947 := by exact prefixLift 2876947
  have htrace : WordTrace (prefixWord ++ tailWord_2876947) baseStart_2876947 baseEnd_2876947 := by
    simpa [prefixWord, tailWord_2876947, baseEnd_2876947] using wordTrace_append hprefix tailTrace_2876947
  have hstable : (prefixWord ++ tailWord_2876947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876947).length < 2 ^ (prefixWord ++ tailWord_2876947).sum := by decide
  have hdescent : baseEnd_2876947 < baseStart_2876947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876968 : List Nat := [2, 1, 5, 2, 2, 2, 2, 2, 4]
def baseStart_2876968 : Nat := 118140960795 + 2876968 * 2 ^ 59
def prefixEnd_2876968 : Nat := 4983230072969 + 3 ^ 40 * 2876968 * 2
def baseEnd_2876968 : Nat := 328281647023201129593127

theorem tailTrace_2876968 : CollatzResearch.WordTrace tailWord_2876968 prefixEnd_2876968 328281647023201129593127 := by
  unfold tailWord_2876968
  simp only [CollatzResearch.WordTrace]
  refine ⟨52465821720621878930687779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69954428960829171907583705 52465821720621878930687779)
  ·
    refine ⟨78698732580932818396031669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52465821720621878930687779 78698732580932818396031669)
    ·
      refine ⟨7378006179462451724627969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78698732580932818396031669 7378006179462451724627969)
      ·
        refine ⟨5533504634596838793470977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7378006179462451724627969 5533504634596838793470977)
        ·
          refine ⟨4150128475947629095103233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5533504634596838793470977 4150128475947629095103233)
          ·
            refine ⟨3112596356960721821327425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4150128475947629095103233 3112596356960721821327425)
            ·
              refine ⟨2334447267720541365995569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3112596356960721821327425 2334447267720541365995569)
              ·
                refine ⟨1750835450790406024496677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2334447267720541365995569 1750835450790406024496677)
                ·
                  refine ⟨328281647023201129593127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1750835450790406024496677 328281647023201129593127)
                  ·
                    rfl

theorem cell22_2876968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 2, 4].length) (baseStart_2876968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2876968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2876968 prefixEnd_2876968 := by exact prefixLift 2876968
  have htrace : WordTrace (prefixWord ++ tailWord_2876968) baseStart_2876968 baseEnd_2876968 := by
    simpa [prefixWord, tailWord_2876968, baseEnd_2876968] using wordTrace_append hprefix tailTrace_2876968
  have hstable : (prefixWord ++ tailWord_2876968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876968).length < 2 ^ (prefixWord ++ tailWord_2876968).sum := by decide
  have hdescent : baseEnd_2876968 < baseStart_2876968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876977 : List Nat := [1, 2, 2, 3, 1, 1, 1, 5, 3, 3]
def baseStart_2876977 : Nat := 118140960795 + 2876977 * 2 ^ 59
def prefixEnd_2876977 : Nat := 4983230072969 + 3 ^ 40 * 2876977 * 2
def baseEnd_2876977 : Nat := 984848021953530365304353

theorem tailTrace_2876977 : CollatzResearch.WordTrace tailWord_2876977 prefixEnd_2876977 984848021953530365304353 := by
  unfold tailWord_2876977
  simp only [CollatzResearch.WordTrace]
  refine ⟨104931971698211152398453185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69954647798807434932302123 104931971698211152398453185)
  ·
    refine ⟨78698978773658364298839889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104931971698211152398453185 78698978773658364298839889)
    ·
      refine ⟨59024234080243773224129917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78698978773658364298839889 59024234080243773224129917)
      ·
        refine ⟨22134087780091414959048719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59024234080243773224129917 22134087780091414959048719)
        ·
          refine ⟨33201131670137122438573079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22134087780091414959048719 33201131670137122438573079)
          ·
            refine ⟨49801697505205683657859619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33201131670137122438573079 49801697505205683657859619)
            ·
              refine ⟨74702546257808525486789429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49801697505205683657859619 74702546257808525486789429)
              ·
                refine ⟨7003363711669549264386509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74702546257808525486789429 7003363711669549264386509)
                ·
                  refine ⟨2626261391876080974144941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7003363711669549264386509 2626261391876080974144941)
                  ·
                    refine ⟨984848021953530365304353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2626261391876080974144941 984848021953530365304353)
                    ·
                      rfl

theorem cell22_2876977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 3, 3].length) (baseStart_2876977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2876977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2876977 prefixEnd_2876977 := by exact prefixLift 2876977
  have htrace : WordTrace (prefixWord ++ tailWord_2876977) baseStart_2876977 baseEnd_2876977 := by
    simpa [prefixWord, tailWord_2876977, baseEnd_2876977] using wordTrace_append hprefix tailTrace_2876977
  have hstable : (prefixWord ++ tailWord_2876977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876977).length < 2 ^ (prefixWord ++ tailWord_2876977).sum := by decide
  have hdescent : baseEnd_2876977 < baseStart_2876977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2876998 : List Nat := [6, 1, 1, 1, 3, 2, 1, 1, 2, 4]
def baseStart_2876998 : Nat := 118140960795 + 2876998 * 2 ^ 59
def prefixEnd_2876998 : Nat := 4983230072969 + 3 ^ 40 * 2876998 * 2
def baseEnd_2876998 : Nat := 984855210682693310529289

theorem tailTrace_2876998 : CollatzResearch.WordTrace tailWord_2876998 prefixEnd_2876998 984855210682693310529289 := by
  unfold tailWord_2876998
  simp only [CollatzResearch.WordTrace]
  refine ⟨3279148050972971030780239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 69955158420756715323311765 3279148050972971030780239)
  ·
    refine ⟨4918722076459456546170359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3279148050972971030780239 4918722076459456546170359)
    ·
      refine ⟨7378083114689184819255539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4918722076459456546170359 7378083114689184819255539)
      ·
        refine ⟨11067124672033777228883309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7378083114689184819255539 11067124672033777228883309)
        ·
          refine ⟨4150171752012666460831241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11067124672033777228883309 4150171752012666460831241)
          ·
            refine ⟨3112628814009499845623431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4150171752012666460831241 3112628814009499845623431)
            ·
              refine ⟨4668943221014249768435147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3112628814009499845623431 4668943221014249768435147)
              ·
                refine ⟨7003414831521374652652721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4668943221014249768435147 7003414831521374652652721)
                ·
                  refine ⟨5252561123641030989489541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7003414831521374652652721 5252561123641030989489541)
                  ·
                    refine ⟨984855210682693310529289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5252561123641030989489541 984855210682693310529289)
                    ·
                      rfl

theorem cell22_2876998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_2876998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2876998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2876998 prefixEnd_2876998 := by exact prefixLift 2876998
  have htrace : WordTrace (prefixWord ++ tailWord_2876998) baseStart_2876998 baseEnd_2876998 := by
    simpa [prefixWord, tailWord_2876998, baseEnd_2876998] using wordTrace_append hprefix tailTrace_2876998
  have hstable : (prefixWord ++ tailWord_2876998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2876998).length < 2 ^ (prefixWord ++ tailWord_2876998).sum := by decide
  have hdescent : baseEnd_2876998 < baseStart_2876998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2876998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877067 : List Nat := [1, 1, 1, 1, 4, 1, 3, 1, 6, 3]
def baseStart_2877067 : Nat := 118140960795 + 2877067 * 2 ^ 59
def prefixEnd_2877067 : Nat := 4983230072969 + 3 ^ 40 * 2877067 * 2
def baseEnd_2877067 : Nat := 984878830792800130554077

theorem tailTrace_2877067 : CollatzResearch.WordTrace tailWord_2877067 prefixEnd_2877067 984878830792800130554077 := by
  unfold tailWord_2877067
  simp only [CollatzResearch.WordTrace]
  refine ⟨104935254267885097769229455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69956836178590065179486303 104935254267885097769229455)
  ·
    refine ⟨157402881401827646653844183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104935254267885097769229455 157402881401827646653844183)
    ·
      refine ⟨236104322102741469980766275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157402881401827646653844183 236104322102741469980766275)
      ·
        refine ⟨354156483154112204971149413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236104322102741469980766275 354156483154112204971149413)
        ·
          refine ⟨66404340591396038432090515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 354156483154112204971149413 66404340591396038432090515)
          ·
            refine ⟨99606510887094057648135773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66404340591396038432090515 99606510887094057648135773)
            ·
              refine ⟨37352441582660271618050915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99606510887094057648135773 37352441582660271618050915)
              ·
                refine ⟨56028662373990407427076373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37352441582660271618050915 56028662373990407427076373)
                ·
                  refine ⟨2626343548780800348144205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 56028662373990407427076373 2626343548780800348144205)
                  ·
                    refine ⟨984878830792800130554077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2626343548780800348144205 984878830792800130554077)
                    ·
                      rfl

theorem cell22_2877067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 6, 3].length) (baseStart_2877067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2877067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2877067 prefixEnd_2877067 := by exact prefixLift 2877067
  have htrace : WordTrace (prefixWord ++ tailWord_2877067) baseStart_2877067 baseEnd_2877067 := by
    simpa [prefixWord, tailWord_2877067, baseEnd_2877067] using wordTrace_append hprefix tailTrace_2877067
  have hstable : (prefixWord ++ tailWord_2877067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877067).length < 2 ^ (prefixWord ++ tailWord_2877067).sum := by decide
  have hdescent : baseEnd_2877067 < baseStart_2877067 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877086 : List Nat := [4, 3, 1, 1, 1, 4, 1, 1, 6]
def baseStart_2877086 : Nat := 118140960795 + 2877086 * 2 ^ 59
def prefixEnd_2877086 : Nat := 4983230072969 + 3 ^ 40 * 2877086 * 2
def baseEnd_2877086 : Nat := 328295111627030138109673

theorem tailTrace_2877086 : CollatzResearch.WordTrace tailWord_2877086 prefixEnd_2877086 328295111627030138109673 := by
  unfold tailWord_2877086
  simp only [CollatzResearch.WordTrace]
  refine ⟨13116993406852033001771389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69957298169877509342780741 13116993406852033001771389)
  ·
    refine ⟨4918872527569512375664271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13116993406852033001771389 4918872527569512375664271)
    ·
      refine ⟨7378308791354268563496407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4918872527569512375664271 7378308791354268563496407)
      ·
        refine ⟨11067463187031402845244611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7378308791354268563496407 11067463187031402845244611)
        ·
          refine ⟨16601194780547104267866917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11067463187031402845244611 16601194780547104267866917)
          ·
            refine ⟨3112724021352582050225047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16601194780547104267866917 3112724021352582050225047)
            ·
              refine ⟨4669086032028873075337571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3112724021352582050225047 4669086032028873075337571)
              ·
                refine ⟨7003629048043309613006357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4669086032028873075337571 7003629048043309613006357)
                ·
                  refine ⟨328295111627030138109673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7003629048043309613006357 328295111627030138109673)
                  ·
                    rfl

theorem cell22_2877086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_2877086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2877086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2877086 prefixEnd_2877086 := by exact prefixLift 2877086
  have htrace : WordTrace (prefixWord ++ tailWord_2877086) baseStart_2877086 baseEnd_2877086 := by
    simpa [prefixWord, tailWord_2877086, baseEnd_2877086] using wordTrace_append hprefix tailTrace_2877086
  have hstable : (prefixWord ++ tailWord_2877086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877086).length < 2 ^ (prefixWord ++ tailWord_2877086).sum := by decide
  have hdescent : baseEnd_2877086 < baseStart_2877086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877101 : List Nat := [1, 5, 2, 1, 1, 1, 3, 3, 2, 3]
def baseStart_2877101 : Nat := 118140960795 + 2877101 * 2 ^ 59
def prefixEnd_2877101 : Nat := 4983230072969 + 3 ^ 40 * 2877101 * 2
def baseEnd_2877101 : Nat := 984890469687635375203973

theorem tailTrace_2877101 : CollatzResearch.WordTrace tailWord_2877101 prefixEnd_2877101 984890469687635375203973 := by
  unfold tailWord_2877101
  simp only [CollatzResearch.WordTrace]
  refine ⟨104936494349761921575967157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69957662899841281050644771 104936494349761921575967157)
  ·
    refine ⟨9837796345290180147746921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104936494349761921575967157 9837796345290180147746921)
    ·
      refine ⟨7378347258967635110810191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9837796345290180147746921 7378347258967635110810191)
      ·
        refine ⟨11067520888451452666215287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7378347258967635110810191 11067520888451452666215287)
        ·
          refine ⟨16601281332677178999322931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11067520888451452666215287 16601281332677178999322931)
          ·
            refine ⟨24901921999015768498984397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16601281332677178999322931 24901921999015768498984397)
            ·
              refine ⟨9338220749630913187119149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24901921999015768498984397 9338220749630913187119149)
              ·
                refine ⟨3501832781111592445169681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9338220749630913187119149 3501832781111592445169681)
                ·
                  refine ⟨2626374585833694333877261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3501832781111592445169681 2626374585833694333877261)
                  ·
                    refine ⟨984890469687635375203973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2626374585833694333877261 984890469687635375203973)
                    ·
                      rfl

theorem cell22_2877101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_2877101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2877101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2877101 prefixEnd_2877101 := by exact prefixLift 2877101
  have htrace : WordTrace (prefixWord ++ tailWord_2877101) baseStart_2877101 baseEnd_2877101 := by
    simpa [prefixWord, tailWord_2877101, baseEnd_2877101] using wordTrace_append hprefix tailTrace_2877101
  have hstable : (prefixWord ++ tailWord_2877101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877101).length < 2 ^ (prefixWord ++ tailWord_2877101).sum := by decide
  have hdescent : baseEnd_2877101 < baseStart_2877101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877122 : List Nat := [3, 5, 1, 2, 1, 1, 3, 1, 1, 4]
def baseStart_2877122 : Nat := 118140960795 + 2877122 * 2 ^ 59
def prefixEnd_2877122 : Nat := 4983230072969 + 3 ^ 40 * 2877122 * 2
def baseEnd_2877122 : Nat := 984897658416798320428909

theorem tailTrace_2877122 : CollatzResearch.WordTrace tailWord_2877122 prefixEnd_2877122 984897658416798320428909 := by
  unfold tailWord_2877122
  simp only [CollatzResearch.WordTrace]
  refine ⟨26234315070671460540620405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69958173521790561441654413 26234315070671460540620405)
  ·
    refine ⟨2459467037875449425683163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26234315070671460540620405 2459467037875449425683163)
    ·
      refine ⟨3689200556813174138524745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2459467037875449425683163 3689200556813174138524745)
      ·
        refine ⟨2766900417609880603893559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3689200556813174138524745 2766900417609880603893559)
        ·
          refine ⟨4150350626414820905840339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2766900417609880603893559 4150350626414820905840339)
          ·
            refine ⟨6225525939622231358760509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4150350626414820905840339 6225525939622231358760509)
            ·
              refine ⟨2334572227358336759535191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6225525939622231358760509 2334572227358336759535191)
              ·
                refine ⟨3501858341037505139302787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2334572227358336759535191 3501858341037505139302787)
                ·
                  refine ⟨5252787511556257708954181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3501858341037505139302787 5252787511556257708954181)
                  ·
                    refine ⟨984897658416798320428909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5252787511556257708954181 984897658416798320428909)
                    ·
                      rfl

theorem cell22_2877122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_2877122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2877122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2877122 prefixEnd_2877122 := by exact prefixLift 2877122
  have htrace : WordTrace (prefixWord ++ tailWord_2877122) baseStart_2877122 baseEnd_2877122 := by
    simpa [prefixWord, tailWord_2877122, baseEnd_2877122] using wordTrace_append hprefix tailTrace_2877122
  have hstable : (prefixWord ++ tailWord_2877122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877122).length < 2 ^ (prefixWord ++ tailWord_2877122).sum := by decide
  have hdescent : baseEnd_2877122 < baseStart_2877122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877148 : List Nat := [2, 2, 5, 1, 3, 1, 1, 7]
def baseStart_2877148 : Nat := 118140960795 + 2877148 * 2 ^ 59
def prefixEnd_2877148 : Nat := 4983230072969 + 3 ^ 40 * 2877148 * 2
def baseEnd_2877148 : Nat := 109434062083126991030981

theorem tailTrace_2877148 : CollatzResearch.WordTrace tailWord_2877148 prefixEnd_2877148 109434062083126991030981 := by
  unfold tailWord_2877148
  simp only [CollatzResearch.WordTrace]
  refine ⟨52469104290295824301464049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69958805720394432401952065 52469104290295824301464049)
  ·
    refine ⟨39351828217721868226098037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52469104290295824301464049 39351828217721868226098037)
    ·
      refine ⟨3689233895411425146196691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39351828217721868226098037 3689233895411425146196691)
      ·
        refine ⟨5533850843117137719295037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3689233895411425146196691 5533850843117137719295037)
        ·
          refine ⟨2075194066168926644735639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5533850843117137719295037 2075194066168926644735639)
          ·
            refine ⟨3112791099253389967103459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2075194066168926644735639 3112791099253389967103459)
            ·
              refine ⟨4669186648880084950655189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3112791099253389967103459 4669186648880084950655189)
              ·
                refine ⟨109434062083126991030981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4669186648880084950655189 109434062083126991030981)
                ·
                  rfl

theorem cell22_2877148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 7].length) (baseStart_2877148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2877148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2877148 prefixEnd_2877148 := by exact prefixLift 2877148
  have htrace : WordTrace (prefixWord ++ tailWord_2877148) baseStart_2877148 baseEnd_2877148 := by
    simpa [prefixWord, tailWord_2877148, baseEnd_2877148] using wordTrace_append hprefix tailTrace_2877148
  have hstable : (prefixWord ++ tailWord_2877148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877148).length < 2 ^ (prefixWord ++ tailWord_2877148).sum := by decide
  have hdescent : baseEnd_2877148 < baseStart_2877148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877219 : List Nat := [1, 1, 1, 4, 2, 1, 5, 1, 1, 5]
def baseStart_2877219 : Nat := 118140960795 + 2877219 * 2 ^ 59
def prefixEnd_2877219 : Nat := 4983230072969 + 3 ^ 40 * 2877219 * 2
def baseEnd_2877219 : Nat := 984930863499122400753611

theorem tailTrace_2877219 : CollatzResearch.WordTrace tailWord_2877219 prefixEnd_2877219 984930863499122400753611 := by
  unfold tailWord_2877219
  simp only [CollatzResearch.WordTrace]
  refine ⟨104940798163334427728762711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69960532108889618485841807 104940798163334427728762711)
  ·
    refine ⟨157411197245001641593144067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104940798163334427728762711 157411197245001641593144067)
    ·
      refine ⟨236116795867502462389716101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157411197245001641593144067 236116795867502462389716101)
      ·
        refine ⟨44271899225156711698071769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 236116795867502462389716101 44271899225156711698071769)
        ·
          refine ⟨33203924418867533773553827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44271899225156711698071769 33203924418867533773553827)
          ·
            refine ⟨49805886628301300660330741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33203924418867533773553827 49805886628301300660330741)
            ·
              refine ⟨4669301871403246936906007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49805886628301300660330741 4669301871403246936906007)
              ·
                refine ⟨7003952807104870405359011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4669301871403246936906007 7003952807104870405359011)
                ·
                  refine ⟨10505929210657305608038517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7003952807104870405359011 10505929210657305608038517)
                  ·
                    refine ⟨984930863499122400753611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10505929210657305608038517 984930863499122400753611)
                    ·
                      rfl

theorem cell22_2877219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 5].length) (baseStart_2877219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2877219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2877219 prefixEnd_2877219 := by exact prefixLift 2877219
  have htrace : WordTrace (prefixWord ++ tailWord_2877219) baseStart_2877219 baseEnd_2877219 := by
    simpa [prefixWord, tailWord_2877219, baseEnd_2877219] using wordTrace_append hprefix tailTrace_2877219
  have hstable : (prefixWord ++ tailWord_2877219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877219).length < 2 ^ (prefixWord ++ tailWord_2877219).sum := by decide
  have hdescent : baseEnd_2877219 < baseStart_2877219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877234 : List Nat := [3, 2, 1, 1, 3, 2, 2, 1, 1, 6]
def baseStart_2877234 : Nat := 118140960795 + 2877234 * 2 ^ 59
def prefixEnd_2877234 : Nat := 4983230072969 + 3 ^ 40 * 2877234 * 2
def baseEnd_2877234 : Nat := 984935998305667361628565

theorem tailTrace_2877234 : CollatzResearch.WordTrace tailWord_2877234 prefixEnd_2877234 984935998305667361628565 := by
  unfold tailWord_2877234
  simp only [CollatzResearch.WordTrace]
  refine ⟨26235336314570021322639689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69960896838853390193705837 26235336314570021322639689)
  ·
    refine ⟨19676502235927515991979767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26235336314570021322639689 19676502235927515991979767)
    ·
      refine ⟨29514753353891273987969651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19676502235927515991979767 29514753353891273987969651)
      ·
        refine ⟨44272130030836910981954477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29514753353891273987969651 44272130030836910981954477)
        ·
          refine ⟨16602048761563841618232929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44272130030836910981954477 16602048761563841618232929)
          ·
            refine ⟨12451536571172881213674697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16602048761563841618232929 12451536571172881213674697)
            ·
              refine ⟨9338652428379660910256023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12451536571172881213674697 9338652428379660910256023)
              ·
                refine ⟨14007978642569491365384035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9338652428379660910256023 14007978642569491365384035)
                ·
                  refine ⟨21011967963854237048076053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14007978642569491365384035 21011967963854237048076053)
                  ·
                    refine ⟨984935998305667361628565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21011967963854237048076053 984935998305667361628565)
                    ·
                      rfl

theorem cell22_2877234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_2877234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2877234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2877234 prefixEnd_2877234 := by exact prefixLift 2877234
  have htrace : WordTrace (prefixWord ++ tailWord_2877234) baseStart_2877234 baseEnd_2877234 := by
    simpa [prefixWord, tailWord_2877234, baseEnd_2877234] using wordTrace_append hprefix tailTrace_2877234
  have hstable : (prefixWord ++ tailWord_2877234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877234).length < 2 ^ (prefixWord ++ tailWord_2877234).sum := by decide
  have hdescent : baseEnd_2877234 < baseStart_2877234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877298 : List Nat := [3, 2, 1, 2, 1, 1, 1, 7, 1, 3]
def baseStart_2877298 : Nat := 118140960795 + 2877298 * 2 ^ 59
def prefixEnd_2877298 : Nat := 4983230072969 + 3 ^ 40 * 2877298 * 2
def baseEnd_2877298 : Nat := 984957906813592528028369

theorem tailTrace_2877298 : CollatzResearch.WordTrace tailWord_2877298 prefixEnd_2877298 984957906813592528028369 := by
  unfold tailWord_2877298
  simp only [CollatzResearch.WordTrace]
  refine ⟨26235919882512056055222137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69962453020032149480592365 26235919882512056055222137)
  ·
    refine ⟨19676939911884042041416603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26235919882512056055222137 19676939911884042041416603)
    ·
      refine ⟨29515409867826063062124905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19676939911884042041416603 29515409867826063062124905)
      ·
        refine ⟨22136557400869547296593679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29515409867826063062124905 22136557400869547296593679)
        ·
          refine ⟨33204836101304320944890519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22136557400869547296593679 33204836101304320944890519)
          ·
            refine ⟨49807254151956481417335779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33204836101304320944890519 49807254151956481417335779)
            ·
              refine ⟨74710881227934722126003669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49807254151956481417335779 74710881227934722126003669)
              ·
                refine ⟨1751036278779720049828211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 74710881227934722126003669 1751036278779720049828211)
                ·
                  refine ⟨2626554418169580074742317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1751036278779720049828211 2626554418169580074742317)
                  ·
                    refine ⟨984957906813592528028369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2626554418169580074742317 984957906813592528028369)
                    ·
                      rfl

theorem cell22_2877298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 7, 1, 3].length) (baseStart_2877298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2877298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2877298 prefixEnd_2877298 := by exact prefixLift 2877298
  have htrace : WordTrace (prefixWord ++ tailWord_2877298) baseStart_2877298 baseEnd_2877298 := by
    simpa [prefixWord, tailWord_2877298, baseEnd_2877298] using wordTrace_append hprefix tailTrace_2877298
  have hstable : (prefixWord ++ tailWord_2877298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877298).length < 2 ^ (prefixWord ++ tailWord_2877298).sum := by decide
  have hdescent : baseEnd_2877298 < baseStart_2877298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877309 : List Nat := [1, 4, 1, 1, 2, 1, 1, 4, 2, 5]
def baseStart_2877309 : Nat := 118140960795 + 2877309 * 2 ^ 59
def prefixEnd_2877309 : Nat := 4983230072969 + 3 ^ 40 * 2877309 * 2
def baseEnd_2877309 : Nat := 984961672338392166003335

theorem tailTrace_2877309 : CollatzResearch.WordTrace tailWord_2877309 prefixEnd_2877309 984961672338392166003335 := by
  unfold tailWord_2877309
  simp only [CollatzResearch.WordTrace]
  refine ⟨104944080733008373099538981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69962720488672248733025987 104944080733008373099538981)
  ·
    refine ⟨19677015137439069956163559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104944080733008373099538981 19677015137439069956163559)
    ·
      refine ⟨29515522706158604934245339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19677015137439069956163559 29515522706158604934245339)
      ·
        refine ⟨44273284059237907401368009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29515522706158604934245339 44273284059237907401368009)
        ·
          refine ⟨33204963044428430551026007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44273284059237907401368009 33204963044428430551026007)
          ·
            refine ⟨49807444566642645826539011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33204963044428430551026007 49807444566642645826539011)
            ·
              refine ⟨74711166849963968739808517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49807444566642645826539011 74711166849963968739808517)
              ·
                refine ⟨14008343784368244138714097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74711166849963968739808517 14008343784368244138714097)
                ·
                  refine ⟨10506257838276183104035573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14008343784368244138714097 10506257838276183104035573)
                  ·
                    refine ⟨984961672338392166003335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10506257838276183104035573 984961672338392166003335)
                    ·
                      rfl

theorem cell22_2877309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_2877309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2877309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2877309 prefixEnd_2877309 := by exact prefixLift 2877309
  have htrace : WordTrace (prefixWord ++ tailWord_2877309) baseStart_2877309 baseEnd_2877309 := by
    simpa [prefixWord, tailWord_2877309, baseEnd_2877309] using wordTrace_append hprefix tailTrace_2877309
  have hstable : (prefixWord ++ tailWord_2877309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877309).length < 2 ^ (prefixWord ++ tailWord_2877309).sum := by decide
  have hdescent : baseEnd_2877309 < baseStart_2877309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877315 : List Nat := [1, 1, 1, 3, 4, 2, 4, 2, 1, 3]
def baseStart_2877315 : Nat := 118140960795 + 2877315 * 2 ^ 59
def prefixEnd_2877315 : Nat := 4983230072969 + 3 ^ 40 * 2877315 * 2
def baseEnd_2877315 : Nat := 984963726261010150353317

theorem tailTrace_2877315 : CollatzResearch.WordTrace tailWord_2877315 prefixEnd_2877315 984963726261010150353317 := by
  unfold tailWord_2877315
  simp only [CollatzResearch.WordTrace]
  refine ⟨104944299570986636124257399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69962866380657757416171599 104944299570986636124257399)
  ·
    refine ⟨157416449356479954186386099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104944299570986636124257399 157416449356479954186386099)
    ·
      refine ⟨236124674034719931279579149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157416449356479954186386099 236124674034719931279579149)
      ·
        refine ⟨88546752763019974229842181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236124674034719931279579149 88546752763019974229842181)
        ·
          refine ⟨16602516143066245168095409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88546752763019974229842181 16602516143066245168095409)
          ·
            refine ⟨12451887107299683876071557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16602516143066245168095409 12451887107299683876071557)
            ·
              refine ⟨2334728832618690726763417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12451887107299683876071557 2334728832618690726763417)
              ·
                refine ⟨1751046624464018045072563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2334728832618690726763417 1751046624464018045072563)
                ·
                  refine ⟨2626569936696027067608845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1751046624464018045072563 2626569936696027067608845)
                  ·
                    refine ⟨984963726261010150353317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2626569936696027067608845 984963726261010150353317)
                    ·
                      rfl

theorem cell22_2877315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 2, 1, 3].length) (baseStart_2877315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2877315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2877315 prefixEnd_2877315 := by exact prefixLift 2877315
  have htrace : WordTrace (prefixWord ++ tailWord_2877315) baseStart_2877315 baseEnd_2877315 := by
    simpa [prefixWord, tailWord_2877315, baseEnd_2877315] using wordTrace_append hprefix tailTrace_2877315
  have hstable : (prefixWord ++ tailWord_2877315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877315).length < 2 ^ (prefixWord ++ tailWord_2877315).sum := by decide
  have hdescent : baseEnd_2877315 < baseStart_2877315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877341 : List Nat := [1, 4, 2, 1, 2, 2, 2, 1, 3, 4]
def baseStart_2877341 : Nat := 118140960795 + 2877341 * 2 ^ 59
def prefixEnd_2877341 : Nat := 4983230072969 + 3 ^ 40 * 2877341 * 2
def baseEnd_2877341 : Nat := 984972626592354749203237

theorem tailTrace_2877341 : CollatzResearch.WordTrace tailWord_2877341 prefixEnd_2877341 984972626592354749203237 := by
  unfold tailWord_2877341
  simp only [CollatzResearch.WordTrace]
  refine ⟨104945247868892442564703877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69963498579261628376469251 104945247868892442564703877)
  ·
    refine ⟨19677233975417332980881977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104945247868892442564703877 19677233975417332980881977)
    ·
      refine ⟨14757925481562999735661483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19677233975417332980881977 14757925481562999735661483)
      ·
        refine ⟨22136888222344499603492225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14757925481562999735661483 22136888222344499603492225)
        ·
          refine ⟨16602666166758374702619169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22136888222344499603492225 16602666166758374702619169)
          ·
            refine ⟨12451999625068781026964377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16602666166758374702619169 12451999625068781026964377)
            ·
              refine ⟨9338999718801585770223283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12451999625068781026964377 9338999718801585770223283)
              ·
                refine ⟨14008499578202378655334925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9338999718801585770223283 14008499578202378655334925)
                ·
                  refine ⟨5253187341825891995750597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14008499578202378655334925 5253187341825891995750597)
                  ·
                    refine ⟨984972626592354749203237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5253187341825891995750597 984972626592354749203237)
                    ·
                      rfl

theorem cell22_2877341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_2877341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2877341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2877341 prefixEnd_2877341 := by exact prefixLift 2877341
  have htrace : WordTrace (prefixWord ++ tailWord_2877341) baseStart_2877341 baseEnd_2877341 := by
    simpa [prefixWord, tailWord_2877341, baseEnd_2877341] using wordTrace_append hprefix tailTrace_2877341
  have hstable : (prefixWord ++ tailWord_2877341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877341).length < 2 ^ (prefixWord ++ tailWord_2877341).sum := by decide
  have hdescent : baseEnd_2877341 < baseStart_2877341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877373 : List Nat := [1, 4, 1, 2, 3, 1, 2, 4, 4]
def baseStart_2877373 : Nat := 118140960795 + 2877373 * 2 ^ 59
def prefixEnd_2877373 : Nat := 4983230072969 + 3 ^ 40 * 2877373 * 2
def baseEnd_2877373 : Nat := 328327860282105777467713

theorem tailTrace_2877373 : CollatzResearch.WordTrace tailWord_2877373 prefixEnd_2877373 328327860282105777467713 := by
  unfold tailWord_2877373
  simp only [CollatzResearch.WordTrace]
  refine ⟨104946415004776512029868773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69964276669851008019912515 104946415004776512029868773)
  ·
    refine ⟨19677452813395596005600395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104946415004776512029868773 19677452813395596005600395)
    ·
      refine ⟨29516179220093394008400593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19677452813395596005600395 29516179220093394008400593)
      ·
        refine ⟨22137134415070045506300445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29516179220093394008400593 22137134415070045506300445)
        ·
          refine ⟨8301425405651267064862667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22137134415070045506300445 8301425405651267064862667)
          ·
            refine ⟨12452138108476900597294001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8301425405651267064862667 12452138108476900597294001)
            ·
              refine ⟨9339103581357675447970501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12452138108476900597294001 9339103581357675447970501)
              ·
                refine ⟨1751081921504564146494469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9339103581357675447970501 1751081921504564146494469)
                ·
                  refine ⟨328327860282105777467713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1751081921504564146494469 328327860282105777467713)
                  ·
                    rfl

theorem cell22_2877373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 4, 4].length) (baseStart_2877373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2877373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2877373 prefixEnd_2877373 := by exact prefixLift 2877373
  have htrace : WordTrace (prefixWord ++ tailWord_2877373) baseStart_2877373 baseEnd_2877373 := by
    simpa [prefixWord, tailWord_2877373, baseEnd_2877373] using wordTrace_append hprefix tailTrace_2877373
  have hstable : (prefixWord ++ tailWord_2877373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877373).length < 2 ^ (prefixWord ++ tailWord_2877373).sum := by decide
  have hdescent : baseEnd_2877373 < baseStart_2877373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877388 : List Nat := [2, 2, 1, 4, 1, 4, 1, 1, 1, 5]
def baseStart_2877388 : Nat := 118140960795 + 2877388 * 2 ^ 59
def prefixEnd_2877388 : Nat := 4983230072969 + 3 ^ 40 * 2877388 * 2
def baseEnd_2877388 : Nat := 984988715652862293278093

theorem tailTrace_2877388 : CollatzResearch.WordTrace tailWord_2877388 prefixEnd_2877388 984988715652862293278093 := by
  unfold tailWord_2877388
  simp only [CollatzResearch.WordTrace]
  refine ⟨52473481049861084795832409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69964641399814779727776545 52473481049861084795832409)
  ·
    refine ⟨39355110787395813596874307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52473481049861084795832409 39355110787395813596874307)
    ·
      refine ⟨59032666181093720395311461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39355110787395813596874307 59032666181093720395311461)
      ·
        refine ⟨11068624908955072574120899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59032666181093720395311461 11068624908955072574120899)
        ·
          refine ⟨16602937363432608861181349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11068624908955072574120899 16602937363432608861181349)
          ·
            refine ⟨3113050755643614161471503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16602937363432608861181349 3113050755643614161471503)
            ·
              refine ⟨4669576133465421242207255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3113050755643614161471503 4669576133465421242207255)
              ·
                refine ⟨7004364200198131863310883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4669576133465421242207255 7004364200198131863310883)
                ·
                  refine ⟨10506546300297197794966325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7004364200198131863310883 10506546300297197794966325)
                  ·
                    refine ⟨984988715652862293278093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10506546300297197794966325 984988715652862293278093)
                    ·
                      rfl

theorem cell22_2877388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 1, 5].length) (baseStart_2877388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2877388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2877388 prefixEnd_2877388 := by exact prefixLift 2877388
  have htrace : WordTrace (prefixWord ++ tailWord_2877388) baseStart_2877388 baseEnd_2877388 := by
    simpa [prefixWord, tailWord_2877388, baseEnd_2877388] using wordTrace_append hprefix tailTrace_2877388
  have hstable : (prefixWord ++ tailWord_2877388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877388).length < 2 ^ (prefixWord ++ tailWord_2877388).sum := by decide
  have hdescent : baseEnd_2877388 < baseStart_2877388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877399 : List Nat := [1, 1, 3, 2, 1, 1, 3, 1, 2, 7]
def baseStart_2877399 : Nat := 118140960795 + 2877399 * 2 ^ 59
def prefixEnd_2877399 : Nat := 4983230072969 + 3 ^ 40 * 2877399 * 2
def baseEnd_2877399 : Nat := 984992481177661931253059

theorem tailTrace_2877399 : CollatzResearch.WordTrace tailWord_2877399 prefixEnd_2877399 984992481177661931253059 := by
  unfold tailWord_2877399
  simp only [CollatzResearch.WordTrace]
  refine ⟨104947363302682318470315251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69964908868454878980210167 104947363302682318470315251)
  ·
    refine ⟨157421044954023477705472877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104947363302682318470315251 157421044954023477705472877)
    ·
      refine ⟨59032891857758804139552329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157421044954023477705472877 59032891857758804139552329)
      ·
        refine ⟨44274668893319103104664247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59032891857758804139552329 44274668893319103104664247)
        ·
          refine ⟨66412003339978654656996371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44274668893319103104664247 66412003339978654656996371)
          ·
            refine ⟨99618005009967981985494557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66412003339978654656996371 99618005009967981985494557)
            ·
              refine ⟨37356751878737993244560459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99618005009967981985494557 37356751878737993244560459)
              ·
                refine ⟨56035127818106989866840689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37356751878737993244560459 56035127818106989866840689)
                ·
                  refine ⟨42026345863580242400130517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56035127818106989866840689 42026345863580242400130517)
                  ·
                    refine ⟨984992481177661931253059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42026345863580242400130517 984992481177661931253059)
                    ·
                      rfl

theorem cell22_2877399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_2877399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2877399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2877399 prefixEnd_2877399 := by exact prefixLift 2877399
  have htrace : WordTrace (prefixWord ++ tailWord_2877399) baseStart_2877399 baseEnd_2877399 := by
    simpa [prefixWord, tailWord_2877399, baseEnd_2877399] using wordTrace_append hprefix tailTrace_2877399
  have hstable : (prefixWord ++ tailWord_2877399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877399).length < 2 ^ (prefixWord ++ tailWord_2877399).sum := by decide
  have hdescent : baseEnd_2877399 < baseStart_2877399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877401 : List Nat := [1, 2, 1, 2, 6, 1, 1, 8]
def baseStart_2877401 : Nat := 118140960795 + 2877401 * 2 ^ 59
def prefixEnd_2877401 : Nat := 4983230072969 + 3 ^ 40 * 2877401 * 2
def baseEnd_2877401 : Nat := 109443685090948288078117

theorem tailTrace_2877401 : CollatzResearch.WordTrace tailWord_2877401 prefixEnd_2877401 109443685090948288078117 := by
  unfold tailWord_2877401
  simp only [CollatzResearch.WordTrace]
  refine ⟨104947436248675072811888057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69964957499116715207925371 104947436248675072811888057)
  ·
    refine ⟨78710577186506304608916043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104947436248675072811888057 78710577186506304608916043)
    ·
      refine ⟨118065865779759456913374065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78710577186506304608916043 118065865779759456913374065)
      ·
        refine ⟨88549399334819592685030549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118065865779759456913374065 88549399334819592685030549)
        ·
          refine ⟨4150753093819668407110807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 88549399334819592685030549 4150753093819668407110807)
          ·
            refine ⟨6226129640729502610666211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4150753093819668407110807 6226129640729502610666211)
            ·
              refine ⟨9339194461094253915999317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6226129640729502610666211 9339194461094253915999317)
              ·
                refine ⟨109443685090948288078117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9339194461094253915999317 109443685090948288078117)
                ·
                  rfl

theorem cell22_2877401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 8].length) (baseStart_2877401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2877401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2877401 prefixEnd_2877401 := by exact prefixLift 2877401
  have htrace : WordTrace (prefixWord ++ tailWord_2877401) baseStart_2877401 baseEnd_2877401 := by
    simpa [prefixWord, tailWord_2877401, baseEnd_2877401] using wordTrace_append hprefix tailTrace_2877401
  have hstable : (prefixWord ++ tailWord_2877401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877401).length < 2 ^ (prefixWord ++ tailWord_2877401).sum := by decide
  have hdescent : baseEnd_2877401 < baseStart_2877401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877433 : List Nat := [1, 2, 1, 3, 1, 4, 3, 1, 3, 3]
def baseStart_2877433 : Nat := 118140960795 + 2877433 * 2 ^ 59
def prefixEnd_2877433 : Nat := 4983230072969 + 3 ^ 40 * 2877433 * 2
def baseEnd_2877433 : Nat := 985004120072497175902955

theorem tailTrace_2877433 : CollatzResearch.WordTrace tailWord_2877433 prefixEnd_2877433 985004120072497175902955 := by
  unfold tailWord_2877433
  simp only [CollatzResearch.WordTrace]
  refine ⟨104948603384559142277052953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69965735589706094851368635 104948603384559142277052953)
  ·
    refine ⟨78711452538419356707789715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104948603384559142277052953 78711452538419356707789715)
    ·
      refine ⟨118067178807629035061684573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78711452538419356707789715 118067178807629035061684573)
      ·
        refine ⟨44275192052860888148131715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118067178807629035061684573 44275192052860888148131715)
        ·
          refine ⟨66412788079291332222197573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44275192052860888148131715 66412788079291332222197573)
          ·
            refine ⟨12452397764867124791662045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66412788079291332222197573 12452397764867124791662045)
            ·
              refine ⟨4669649161825171796873267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12452397764867124791662045 4669649161825171796873267)
              ·
                refine ⟨7004473742737757695309901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4669649161825171796873267 7004473742737757695309901)
                ·
                  refine ⟨2626677653526659135741213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7004473742737757695309901 2626677653526659135741213)
                  ·
                    refine ⟨985004120072497175902955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2626677653526659135741213 985004120072497175902955)
                    ·
                      rfl

theorem cell22_2877433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 3, 3].length) (baseStart_2877433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2877433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2877433 prefixEnd_2877433 := by exact prefixLift 2877433
  have htrace : WordTrace (prefixWord ++ tailWord_2877433) baseStart_2877433 baseEnd_2877433 := by
    simpa [prefixWord, tailWord_2877433, baseEnd_2877433] using wordTrace_append hprefix tailTrace_2877433
  have hstable : (prefixWord ++ tailWord_2877433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877433).length < 2 ^ (prefixWord ++ tailWord_2877433).sum := by decide
  have hdescent : baseEnd_2877433 < baseStart_2877433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877510 : List Nat := [6, 1, 1, 1, 1, 1, 1, 3, 3, 4]
def baseStart_2877510 : Nat := 118140960795 + 2877510 * 2 ^ 59
def prefixEnd_2877510 : Nat := 4983230072969 + 3 ^ 40 * 2877510 * 2
def baseEnd_2877510 : Nat := 985030478746094641727719

theorem tailTrace_2877510 : CollatzResearch.WordTrace tailWord_2877510 prefixEnd_2877510 985030478746094641727719 := by
  unfold tailWord_2877510
  simp only [CollatzResearch.WordTrace]
  refine ⟨3279731618915005763362687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 69967607870186789618403989 3279731618915005763362687)
  ·
    refine ⟨4919597428372508645044031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3279731618915005763362687 4919597428372508645044031)
    ·
      refine ⟨7379396142558762967566047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4919597428372508645044031 7379396142558762967566047)
      ·
        refine ⟨11069094213838144451349071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7379396142558762967566047 11069094213838144451349071)
        ·
          refine ⟨16603641320757216677023607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11069094213838144451349071 16603641320757216677023607)
          ·
            refine ⟨24905461981135825015535411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16603641320757216677023607 24905461981135825015535411)
            ·
              refine ⟨37358192971703737523303117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24905461981135825015535411 37358192971703737523303117)
              ·
                refine ⟨14009322364388901571238669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37358192971703737523303117 14009322364388901571238669)
                ·
                  refine ⟨5253495886645838089214501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14009322364388901571238669 5253495886645838089214501)
                  ·
                    refine ⟨985030478746094641727719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5253495886645838089214501 985030478746094641727719)
                    ·
                      rfl

theorem cell22_2877510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_2877510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2877510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2877510 prefixEnd_2877510 := by exact prefixLift 2877510
  have htrace : WordTrace (prefixWord ++ tailWord_2877510) baseStart_2877510 baseEnd_2877510 := by
    simpa [prefixWord, tailWord_2877510, baseEnd_2877510] using wordTrace_append hprefix tailTrace_2877510
  have hstable : (prefixWord ++ tailWord_2877510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877510).length < 2 ^ (prefixWord ++ tailWord_2877510).sum := by decide
  have hdescent : baseEnd_2877510 < baseStart_2877510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877525 : List Nat := [1, 3, 2, 2, 1, 4, 2, 3, 4]
def baseStart_2877525 : Nat := 118140960795 + 2877525 * 2 ^ 59
def prefixEnd_2877525 : Nat := 4983230072969 + 3 ^ 40 * 2877525 * 2
def baseEnd_2877525 : Nat := 328345204517546534200891

theorem tailTrace_2877525 : CollatzResearch.WordTrace tailWord_2877525 prefixEnd_2877525 328345204517546534200891 := by
  unfold tailWord_2877525
  simp only [CollatzResearch.WordTrace]
  refine ⟨104951958900225841989402029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69967972600150561326268019 104951958900225841989402029)
  ·
    refine ⟨39356984587584690746025761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104951958900225841989402029 39356984587584690746025761)
    ·
      refine ⟨29517738440688518059519321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39356984587584690746025761 29517738440688518059519321)
      ·
        refine ⟨22138303830516388544639491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29517738440688518059519321 22138303830516388544639491)
        ·
          refine ⟨33207455745774582816959237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22138303830516388544639491 33207455745774582816959237)
          ·
            refine ⟨6226397952332734278179857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33207455745774582816959237 6226397952332734278179857)
            ·
              refine ⟨4669798464249550708634893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6226397952332734278179857 4669798464249550708634893)
              ·
                refine ⟨1751174424093581515738085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4669798464249550708634893 1751174424093581515738085)
                ·
                  refine ⟨328345204517546534200891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1751174424093581515738085 328345204517546534200891)
                  ·
                    rfl

theorem cell22_2877525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 3, 4].length) (baseStart_2877525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2877525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2877525 prefixEnd_2877525 := by exact prefixLift 2877525
  have htrace : WordTrace (prefixWord ++ tailWord_2877525) baseStart_2877525 baseEnd_2877525 := by
    simpa [prefixWord, tailWord_2877525, baseEnd_2877525] using wordTrace_append hprefix tailTrace_2877525
  have hstable : (prefixWord ++ tailWord_2877525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877525).length < 2 ^ (prefixWord ++ tailWord_2877525).sum := by decide
  have hdescent : baseEnd_2877525 < baseStart_2877525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877536 : List Nat := [2, 1, 1, 3, 2, 4, 9]
def baseStart_2877536 : Nat := 118140960795 + 2877536 * 2 ^ 59
def prefixEnd_2877536 : Nat := 4983230072969 + 3 ^ 40 * 2877536 * 2
def baseEnd_2877536 : Nat := 36482939965831082984357

theorem tailTrace_2877536 : CollatzResearch.WordTrace tailWord_2877536 prefixEnd_2877536 36482939965831082984357 := by
  unfold tailWord_2877536
  simp only [CollatzResearch.WordTrace]
  refine ⟨52476180051592995434026231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69968240068790660578701641 52476180051592995434026231)
  ·
    refine ⟨78714270077389493151039347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52476180051592995434026231 78714270077389493151039347)
    ·
      refine ⟨118071405116084239726559021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78714270077389493151039347 118071405116084239726559021)
      ·
        refine ⟨44276776918531589897459633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118071405116084239726559021 44276776918531589897459633)
        ·
          refine ⟨33207582688898692423094725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44276776918531589897459633 33207582688898692423094725)
          ·
            refine ⟨6226421754168504829330261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33207582688898692423094725 6226421754168504829330261)
            ·
              refine ⟨36482939965831082984357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6226421754168504829330261 36482939965831082984357)
              ·
                rfl

theorem cell22_2877536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 9].length) (baseStart_2877536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2877536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2877536 prefixEnd_2877536 := by exact prefixLift 2877536
  have htrace : WordTrace (prefixWord ++ tailWord_2877536) baseStart_2877536 baseEnd_2877536 := by
    simpa [prefixWord, tailWord_2877536, baseEnd_2877536] using wordTrace_append hprefix tailTrace_2877536
  have hstable : (prefixWord ++ tailWord_2877536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877536).length < 2 ^ (prefixWord ++ tailWord_2877536).sum := by decide
  have hdescent : baseEnd_2877536 < baseStart_2877536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877540 : List Nat := [2, 3, 1, 1, 2, 1, 5, 2, 2, 3]
def baseStart_2877540 : Nat := 118140960795 + 2877540 * 2 ^ 59
def prefixEnd_2877540 : Nat := 4983230072969 + 3 ^ 40 * 2877540 * 2
def baseEnd_2877540 : Nat := 985040748359184563477627

theorem tailTrace_2877540 : CollatzResearch.WordTrace tailWord_2877540 prefixEnd_2877540 985040748359184563477627 := by
  unfold tailWord_2877540
  simp only [CollatzResearch.WordTrace]
  refine ⟨52476252997585749775599037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69968337330114333034132049 52476252997585749775599037)
  ·
    refine ⟨19678594874094656165849639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52476252997585749775599037 19678594874094656165849639)
    ·
      refine ⟨29517892311141984248774459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19678594874094656165849639 29517892311141984248774459)
      ·
        refine ⟨44276838466712976373161689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29517892311141984248774459 44276838466712976373161689)
        ·
          refine ⟨33207628850034732279871267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44276838466712976373161689 33207628850034732279871267)
          ·
            refine ⟨49811443275052098419806901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33207628850034732279871267 49811443275052098419806901)
            ·
              refine ⟨4669822807036134226856897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49811443275052098419806901 4669822807036134226856897)
              ·
                refine ⟨3502367105277100670142673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4669822807036134226856897 3502367105277100670142673)
                ·
                  refine ⟨2626775328957825502607005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3502367105277100670142673 2626775328957825502607005)
                  ·
                    refine ⟨985040748359184563477627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2626775328957825502607005 985040748359184563477627)
                    ·
                      rfl

theorem cell22_2877540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 2, 2, 3].length) (baseStart_2877540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2877540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2877540 prefixEnd_2877540 := by exact prefixLift 2877540
  have htrace : WordTrace (prefixWord ++ tailWord_2877540) baseStart_2877540 baseEnd_2877540 := by
    simpa [prefixWord, tailWord_2877540, baseEnd_2877540] using wordTrace_append hprefix tailTrace_2877540
  have hstable : (prefixWord ++ tailWord_2877540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877540).length < 2 ^ (prefixWord ++ tailWord_2877540).sum := by decide
  have hdescent : baseEnd_2877540 < baseStart_2877540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877602 : List Nat := [3, 3, 1, 3, 1, 1, 3, 1, 3, 3]
def baseStart_2877602 : Nat := 118140960795 + 2877602 * 2 ^ 59
def prefixEnd_2877602 : Nat := 4983230072969 + 3 ^ 40 * 2877602 * 2
def baseEnd_2877602 : Nat := 985061972226237068427437

theorem tailTrace_2877602 : CollatzResearch.WordTrace tailWord_2877602 prefixEnd_2877602 985061972226237068427437 := by
  unfold tailWord_2877602
  simp only [CollatzResearch.WordTrace]
  refine ⟨26238691830236721034988765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69969844880631256093303373 26238691830236721034988765)
  ·
    refine ⟨9839509436338770388120787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26238691830236721034988765 9839509436338770388120787)
    ·
      refine ⟨14759264154508155582181181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9839509436338770388120787 14759264154508155582181181)
      ·
        refine ⟨5534724057940558343317943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14759264154508155582181181 5534724057940558343317943)
        ·
          refine ⟨8302086086910837514976915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5534724057940558343317943 8302086086910837514976915)
          ·
            refine ⟨12453129130366256272465373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8302086086910837514976915 12453129130366256272465373)
            ·
              refine ⟨4669923423887346102174515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12453129130366256272465373 4669923423887346102174515)
              ·
                refine ⟨7004885135831019153261773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4669923423887346102174515 7004885135831019153261773)
                ·
                  refine ⟨2626831925936632182473165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7004885135831019153261773 2626831925936632182473165)
                  ·
                    refine ⟨985061972226237068427437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2626831925936632182473165 985061972226237068427437)
                    ·
                      rfl

theorem cell22_2877602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_2877602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2877602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2877602 prefixEnd_2877602 := by exact prefixLift 2877602
  have htrace : WordTrace (prefixWord ++ tailWord_2877602) baseStart_2877602 baseEnd_2877602 := by
    simpa [prefixWord, tailWord_2877602, baseEnd_2877602] using wordTrace_append hprefix tailTrace_2877602
  have hstable : (prefixWord ++ tailWord_2877602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877602).length < 2 ^ (prefixWord ++ tailWord_2877602).sum := by decide
  have hdescent : baseEnd_2877602 < baseStart_2877602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877653 : List Nat := [1, 3, 2, 4, 3, 1, 2, 2, 1, 3]
def baseStart_2877653 : Nat := 118140960795 + 2877653 * 2 ^ 59
def prefixEnd_2877653 : Nat := 4983230072969 + 3 ^ 40 * 2877653 * 2
def baseEnd_2877653 : Nat := 985079430568489935402281

theorem tailTrace_2877653 : CollatzResearch.WordTrace tailWord_2877653 prefixEnd_2877653 985079430568489935402281 := by
  unfold tailWord_2877653
  simp only [CollatzResearch.WordTrace]
  refine ⟨104956627443762119850061613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69971084962508079900041075 104956627443762119850061613)
  ·
    refine ⟨39358735291410794943773105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104956627443762119850061613 39358735291410794943773105)
    ·
      refine ⟨29519051468558096207829829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39358735291410794943773105 29519051468558096207829829)
      ·
        refine ⟨5534822150354643038968093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29519051468558096207829829 5534822150354643038968093)
        ·
          refine ⟨2075558306382991139613035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5534822150354643038968093 2075558306382991139613035)
          ·
            refine ⟨3113337459574486709419553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2075558306382991139613035 3113337459574486709419553)
            ·
              refine ⟨2335003094680865032064665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3113337459574486709419553 2335003094680865032064665)
              ·
                refine ⟨1751252321010648774048499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2335003094680865032064665 1751252321010648774048499)
                ·
                  refine ⟨2626878481515973161072749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1751252321010648774048499 2626878481515973161072749)
                  ·
                    refine ⟨985079430568489935402281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2626878481515973161072749 985079430568489935402281)
                    ·
                      rfl

theorem cell22_2877653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 2, 1, 3].length) (baseStart_2877653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2877653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2877653 prefixEnd_2877653 := by exact prefixLift 2877653
  have htrace : WordTrace (prefixWord ++ tailWord_2877653) baseStart_2877653 baseEnd_2877653 := by
    simpa [prefixWord, tailWord_2877653, baseEnd_2877653] using wordTrace_append hprefix tailTrace_2877653
  have hstable : (prefixWord ++ tailWord_2877653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877653).length < 2 ^ (prefixWord ++ tailWord_2877653).sum := by decide
  have hdescent : baseEnd_2877653 < baseStart_2877653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877675 : List Nat := [1, 1, 1, 1, 2, 5, 1, 5, 2, 3]
def baseStart_2877675 : Nat := 118140960795 + 2877675 * 2 ^ 59
def prefixEnd_2877675 : Nat := 4983230072969 + 3 ^ 40 * 2877675 * 2
def baseEnd_2877675 : Nat := 985086961618089211352213

theorem tailTrace_2877675 : CollatzResearch.WordTrace tailWord_2877675 prefixEnd_2877675 985086961618089211352213 := by
  unfold tailWord_2877675
  simp only [CollatzResearch.WordTrace]
  refine ⟨104957429849682417607362479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69971619899788278404908319 104957429849682417607362479)
  ·
    refine ⟨157436144774523626411043719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104957429849682417607362479 157436144774523626411043719)
    ·
      refine ⟨236154217161785439616565579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157436144774523626411043719 236154217161785439616565579)
      ·
        refine ⟨354231325742678159424848369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236154217161785439616565579 354231325742678159424848369)
        ·
          refine ⟨265673494307008619568636277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 354231325742678159424848369 265673494307008619568636277)
          ·
            refine ⟨24906890091282058084559651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 265673494307008619568636277 24906890091282058084559651)
            ·
              refine ⟨37360335136923087126839477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24906890091282058084559651 37360335136923087126839477)
              ·
                refine ⟨3502531419086539418141201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37360335136923087126839477 3502531419086539418141201)
                ·
                  refine ⟨2626898564314904563605901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3502531419086539418141201 2626898564314904563605901)
                  ·
                    refine ⟨985086961618089211352213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2626898564314904563605901 985086961618089211352213)
                    ·
                      rfl

theorem cell22_2877675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 5, 2, 3].length) (baseStart_2877675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2877675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2877675 prefixEnd_2877675 := by exact prefixLift 2877675
  have htrace : WordTrace (prefixWord ++ tailWord_2877675) baseStart_2877675 baseEnd_2877675 := by
    simpa [prefixWord, tailWord_2877675, baseEnd_2877675] using wordTrace_append hprefix tailTrace_2877675
  have hstable : (prefixWord ++ tailWord_2877675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877675).length < 2 ^ (prefixWord ++ tailWord_2877675).sum := by decide
  have hdescent : baseEnd_2877675 < baseStart_2877675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877690 : List Nat := [3, 1, 1, 1, 1, 5, 3, 1, 2, 4]
def baseStart_2877690 : Nat := 118140960795 + 2877690 * 2 ^ 59
def prefixEnd_2877690 : Nat := 4983230072969 + 3 ^ 40 * 2877690 * 2
def baseEnd_2877690 : Nat := 985092096424634172227167

theorem tailTrace_2877690 : CollatzResearch.WordTrace tailWord_2877690 prefixEnd_2877690 985092096424634172227167 := by
  unfold tailWord_2877690
  simp only [CollatzResearch.WordTrace]
  refine ⟨26239494236157018792289631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69971984629752050112772349 26239494236157018792289631)
  ·
    refine ⟨39359241354235528188434447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26239494236157018792289631 39359241354235528188434447)
    ·
      refine ⟨59038862031353292282651671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39359241354235528188434447 59038862031353292282651671)
      ·
        refine ⟨88558293047029938423977507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59038862031353292282651671 88558293047029938423977507)
        ·
          refine ⟨132837439570544907635966261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88558293047029938423977507 132837439570544907635966261)
          ·
            refine ⟨12453509959738585090871837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 132837439570544907635966261 12453509959738585090871837)
            ·
              refine ⟨4670066234901969409076939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12453509959738585090871837 4670066234901969409076939)
              ·
                refine ⟨7005099352352954113615409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4670066234901969409076939 7005099352352954113615409)
                ·
                  refine ⟨5253824514264715585211557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7005099352352954113615409 5253824514264715585211557)
                  ·
                    refine ⟨985092096424634172227167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5253824514264715585211557 985092096424634172227167)
                    ·
                      rfl

theorem cell22_2877690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 2, 4].length) (baseStart_2877690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2877690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2877690 prefixEnd_2877690 := by exact prefixLift 2877690
  have htrace : WordTrace (prefixWord ++ tailWord_2877690) baseStart_2877690 baseEnd_2877690 := by
    simpa [prefixWord, tailWord_2877690, baseEnd_2877690] using wordTrace_append hprefix tailTrace_2877690
  have hstable : (prefixWord ++ tailWord_2877690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877690).length < 2 ^ (prefixWord ++ tailWord_2877690).sum := by decide
  have hdescent : baseEnd_2877690 < baseStart_2877690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877754 : List Nat := [3, 1, 1, 1, 4, 2, 3, 3, 1, 3]
def baseStart_2877754 : Nat := 118140960795 + 2877754 * 2 ^ 59
def prefixEnd_2877754 : Nat := 4983230072969 + 3 ^ 40 * 2877754 * 2
def baseEnd_2877754 : Nat := 985114004932559338626971

theorem tailTrace_2877754 : CollatzResearch.WordTrace tailWord_2877754 prefixEnd_2877754 985114004932559338626971 := by
  unfold tailWord_2877754
  simp only [CollatzResearch.WordTrace]
  refine ⟨26240077804099053524872079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69973540810930809399658877 26240077804099053524872079)
  ·
    refine ⟨39360116706148580287308119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26240077804099053524872079 39360116706148580287308119)
    ·
      refine ⟨59040175059222870430962179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39360116706148580287308119 59040175059222870430962179)
      ·
        refine ⟨88560262588834305646443269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59040175059222870430962179 88560262588834305646443269)
        ·
          refine ⟨16605049235406432308708113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88560262588834305646443269 16605049235406432308708113)
          ·
            refine ⟨12453786926554824231531085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16605049235406432308708113 12453786926554824231531085)
            ·
              refine ⟨4670170097458059086824157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12453786926554824231531085 4670170097458059086824157)
              ·
                refine ⟨1751313786546772157559059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4670170097458059086824157 1751313786546772157559059)
                ·
                  refine ⟨2626970679820158236338589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1751313786546772157559059 2626970679820158236338589)
                  ·
                    refine ⟨985114004932559338626971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2626970679820158236338589 985114004932559338626971)
                    ·
                      rfl

theorem cell22_2877754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 3, 1, 3].length) (baseStart_2877754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2877754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2877754 prefixEnd_2877754 := by exact prefixLift 2877754
  have htrace : WordTrace (prefixWord ++ tailWord_2877754) baseStart_2877754 baseEnd_2877754 := by
    simpa [prefixWord, tailWord_2877754, baseEnd_2877754] using wordTrace_append hprefix tailTrace_2877754
  have hstable : (prefixWord ++ tailWord_2877754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877754).length < 2 ^ (prefixWord ++ tailWord_2877754).sum := by decide
  have hdescent : baseEnd_2877754 < baseStart_2877754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877797 : List Nat := [1, 3, 1, 3, 1, 3, 3, 2, 1, 4]
def baseStart_2877797 : Nat := 118140960795 + 2877797 * 2 ^ 59
def prefixEnd_2877797 : Nat := 4983230072969 + 3 ^ 40 * 2877797 * 2
def baseEnd_2877797 : Nat := 985128724711321559801839

theorem tailTrace_2877797 : CollatzResearch.WordTrace tailWord_2877797 prefixEnd_2877797 985128724711321559801839 := by
  unfold tailWord_2877797
  simp only [CollatzResearch.WordTrace]
  refine ⟨104961879555240432443303645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69974586370160288295535763 104961879555240432443303645)
  ·
    refine ⟨39360704833215162166238867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104961879555240432443303645 39360704833215162166238867)
    ·
      refine ⟨59041057249822743249358301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39360704833215162166238867 59041057249822743249358301)
      ·
        refine ⟨22140396468683528718509363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59041057249822743249358301 22140396468683528718509363)
        ·
          refine ⟨33210594703025293077764045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22140396468683528718509363 33210594703025293077764045)
          ·
            refine ⟨12453973013634484904161517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33210594703025293077764045 12453973013634484904161517)
            ·
              refine ⟨4670239880112931839060569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12453973013634484904161517 4670239880112931839060569)
              ·
                refine ⟨3502679910084698879295427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4670239880112931839060569 3502679910084698879295427)
                ·
                  refine ⟨5254019865127048318943141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3502679910084698879295427 5254019865127048318943141)
                  ·
                    refine ⟨985128724711321559801839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5254019865127048318943141 985128724711321559801839)
                    ·
                      rfl

theorem cell22_2877797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 2, 1, 4].length) (baseStart_2877797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2877797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2877797 prefixEnd_2877797 := by exact prefixLift 2877797
  have htrace : WordTrace (prefixWord ++ tailWord_2877797) baseStart_2877797 baseEnd_2877797 := by
    simpa [prefixWord, tailWord_2877797, baseEnd_2877797] using wordTrace_append hprefix tailTrace_2877797
  have hstable : (prefixWord ++ tailWord_2877797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877797).length < 2 ^ (prefixWord ++ tailWord_2877797).sum := by decide
  have hdescent : baseEnd_2877797 < baseStart_2877797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877810 : List Nat := [3, 2, 1, 2, 1, 3, 1, 1, 3, 5]
def baseStart_2877810 : Nat := 118140960795 + 2877810 * 2 ^ 59
def prefixEnd_2877810 : Nat := 4983230072969 + 3 ^ 40 * 2877810 * 2
def baseEnd_2877810 : Nat := 985133174876993859226799

theorem tailTrace_2877810 : CollatzResearch.WordTrace tailWord_2877810 prefixEnd_2877810 985133174876993859226799 := by
  unfold tailWord_2877810
  simp only [CollatzResearch.WordTrace]
  refine ⟨26240588426048333915881721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69974902469462223775684589 26240588426048333915881721)
  ·
    refine ⟨19680441319536250436911291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26240588426048333915881721 19680441319536250436911291)
    ·
      refine ⟨29520661979304375655366937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19680441319536250436911291 29520661979304375655366937)
      ·
        refine ⟨22140496484478281741525203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29520661979304375655366937 22140496484478281741525203)
        ·
          refine ⟨33210744726717422612287805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22140496484478281741525203 33210744726717422612287805)
          ·
            refine ⟨12454029272519033479607927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33210744726717422612287805 12454029272519033479607927)
            ·
              refine ⟨18681043908778550219411891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12454029272519033479607927 18681043908778550219411891)
              ·
                refine ⟨28021565863167825329117837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18681043908778550219411891 28021565863167825329117837)
                ·
                  refine ⟨10508087198687934498419189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28021565863167825329117837 10508087198687934498419189)
                  ·
                    refine ⟨985133174876993859226799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10508087198687934498419189 985133174876993859226799)
                    ·
                      rfl

theorem cell22_2877810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_2877810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2877810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2877810 prefixEnd_2877810 := by exact prefixLift 2877810
  have htrace : WordTrace (prefixWord ++ tailWord_2877810) baseStart_2877810 baseEnd_2877810 := by
    simpa [prefixWord, tailWord_2877810, baseEnd_2877810] using wordTrace_append hprefix tailTrace_2877810
  have hstable : (prefixWord ++ tailWord_2877810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877810).length < 2 ^ (prefixWord ++ tailWord_2877810).sum := by decide
  have hdescent : baseEnd_2877810 < baseStart_2877810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877844 : List Nat := [2, 4, 2, 1, 3, 1, 2, 1, 1, 5]
def baseStart_2877844 : Nat := 118140960795 + 2877844 * 2 ^ 59
def prefixEnd_2877844 : Nat := 4983230072969 + 3 ^ 40 * 2877844 * 2
def baseEnd_2877844 : Nat := 985144813771829103876695

theorem tailTrace_2877844 : CollatzResearch.WordTrace tailWord_2877844 prefixEnd_2877844 985144813771829103876695 := by
  unfold tailWord_2877844
  simp only [CollatzResearch.WordTrace]
  refine ⟨52481796893035079735132293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69975729190713439646843057 52481796893035079735132293)
  ·
    refine ⟨9840336917444077450337305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52481796893035079735132293 9840336917444077450337305)
    ·
      refine ⟨7380252688083058087752979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9840336917444077450337305 7380252688083058087752979)
      ·
        refine ⟨11070379032124587131629469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7380252688083058087752979 11070379032124587131629469)
        ·
          refine ⟨4151392137046720174361051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11070379032124587131629469 4151392137046720174361051)
          ·
            refine ⟨6227088205570080261541577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4151392137046720174361051 6227088205570080261541577)
            ·
              refine ⟨4670316154177560196156183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6227088205570080261541577 4670316154177560196156183)
              ·
                refine ⟨7005474231266340294234275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4670316154177560196156183 7005474231266340294234275)
                ·
                  refine ⟨10508211346899510441351413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7005474231266340294234275 10508211346899510441351413)
                  ·
                    refine ⟨985144813771829103876695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10508211346899510441351413 985144813771829103876695)
                    ·
                      rfl

theorem cell22_2877844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_2877844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2877844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2877844 prefixEnd_2877844 := by exact prefixLift 2877844
  have htrace : WordTrace (prefixWord ++ tailWord_2877844) baseStart_2877844 baseEnd_2877844 := by
    simpa [prefixWord, tailWord_2877844, baseEnd_2877844] using wordTrace_append hprefix tailTrace_2877844
  have hstable : (prefixWord ++ tailWord_2877844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877844).length < 2 ^ (prefixWord ++ tailWord_2877844).sum := by decide
  have hdescent : baseEnd_2877844 < baseStart_2877844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877923 : List Nat := [1, 1, 1, 6, 3, 2, 1, 3, 1, 3]
def baseStart_2877923 : Nat := 118140960795 + 2877923 * 2 ^ 59
def prefixEnd_2877923 : Nat := 4983230072969 + 3 ^ 40 * 2877923 * 2
def baseEnd_2877923 : Nat := 985171857086299231151453

theorem tailTrace_2877923 : CollatzResearch.WordTrace tailWord_2877923 prefixEnd_2877923 985171857086299231151453 := by
  unfold tailWord_2877923
  simp only [CollatzResearch.WordTrace]
  refine ⟨104966475152783955962390423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69977650101855970641593615 104966475152783955962390423)
  ·
    refine ⟨157449712729175933943585635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104966475152783955962390423 157449712729175933943585635)
    ·
      refine ⟨236174569093763900915378453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157449712729175933943585635 236174569093763900915378453)
      ·
        refine ⟨11070682926270182855408365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 236174569093763900915378453 11070682926270182855408365)
        ·
          refine ⟨4151506097351318570778137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11070682926270182855408365 4151506097351318570778137)
          ·
            refine ⟨3113629573013488928083603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4151506097351318570778137 3113629573013488928083603)
            ·
              refine ⟨4670444359520233392125405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3113629573013488928083603 4670444359520233392125405)
              ·
                refine ⟨1751416634820087522047027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4670444359520233392125405 1751416634820087522047027)
                ·
                  refine ⟨2627124952230131283070541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1751416634820087522047027 2627124952230131283070541)
                  ·
                    refine ⟨985171857086299231151453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2627124952230131283070541 985171857086299231151453)
                    ·
                      rfl

theorem cell22_2877923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 3, 1, 3].length) (baseStart_2877923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2877923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2877923 prefixEnd_2877923 := by exact prefixLift 2877923
  have htrace : WordTrace (prefixWord ++ tailWord_2877923) baseStart_2877923 baseEnd_2877923 := by
    simpa [prefixWord, tailWord_2877923, baseEnd_2877923] using wordTrace_append hprefix tailTrace_2877923
  have hstable : (prefixWord ++ tailWord_2877923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877923).length < 2 ^ (prefixWord ++ tailWord_2877923).sum := by decide
  have hdescent : baseEnd_2877923 < baseStart_2877923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877932 : List Nat := [2, 2, 1, 1, 2, 1, 3, 5, 1, 4]
def baseStart_2877932 : Nat := 118140960795 + 2877932 * 2 ^ 59
def prefixEnd_2877932 : Nat := 4983230072969 + 3 ^ 40 * 2877932 * 2
def baseEnd_2877932 : Nat := 985174937970226207676425

theorem tailTrace_2877932 : CollatzResearch.WordTrace tailWord_2877932 prefixEnd_2877932 985174937970226207676425 := by
  unfold tailWord_2877932
  simp only [CollatzResearch.WordTrace]
  refine ⟨52483401704875675249734025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69977868939834233666312033 52483401704875675249734025)
  ·
    refine ⟨39362551278656756437300519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52483401704875675249734025 39362551278656756437300519)
    ·
      refine ⟨59043826917985134655950779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39362551278656756437300519 59043826917985134655950779)
      ·
        refine ⟨88565740376977701983926169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59043826917985134655950779 88565740376977701983926169)
        ·
          refine ⟨66424305282733276487944627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88565740376977701983926169 66424305282733276487944627)
          ·
            refine ⟨99636457924099914731916941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66424305282733276487944627 99636457924099914731916941)
            ·
              refine ⟨37363671721537468024468853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99636457924099914731916941 37363671721537468024468853)
              ·
                refine ⟨3502844223894137627293955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37363671721537468024468853 3502844223894137627293955)
                ·
                  refine ⟨5254266335841206440940933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3502844223894137627293955 5254266335841206440940933)
                  ·
                    refine ⟨985174937970226207676425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5254266335841206440940933 985174937970226207676425)
                    ·
                      rfl

theorem cell22_2877932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 4].length) (baseStart_2877932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2877932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2877932 prefixEnd_2877932 := by exact prefixLift 2877932
  have htrace : WordTrace (prefixWord ++ tailWord_2877932) baseStart_2877932 baseEnd_2877932 := by
    simpa [prefixWord, tailWord_2877932, baseEnd_2877932] using wordTrace_append hprefix tailTrace_2877932
  have hstable : (prefixWord ++ tailWord_2877932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877932).length < 2 ^ (prefixWord ++ tailWord_2877932).sum := by decide
  have hdescent : baseEnd_2877932 < baseStart_2877932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877962 : List Nat := [3, 1, 2, 2, 2, 1, 2, 3, 1, 5]
def baseStart_2877962 : Nat := 118140960795 + 2877962 * 2 ^ 59
def prefixEnd_2877962 : Nat := 4983230072969 + 3 ^ 40 * 2877962 * 2
def baseEnd_2877962 : Nat := 985185207583316129426333

theorem tailTrace_2877962 : CollatzResearch.WordTrace tailWord_2877962 prefixEnd_2877962 985185207583316129426333 := by
  unfold tailWord_2877962
  simp only [CollatzResearch.WordTrace]
  refine ⟨26241974399910666405765035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69978598399761777082040093 26241974399910666405765035)
  ·
    refine ⟨39362961599865999608647553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26241974399910666405765035 39362961599865999608647553)
    ·
      refine ⟨29522221199899499706485665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39362961599865999608647553 29522221199899499706485665)
      ·
        refine ⟨22141665899924624779864249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29522221199899499706485665 22141665899924624779864249)
        ·
          refine ⟨16606249424943468584898187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22141665899924624779864249 16606249424943468584898187)
          ·
            refine ⟨24909374137415202877347281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16606249424943468584898187 24909374137415202877347281)
            ·
              refine ⟨18682030603061402158010461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24909374137415202877347281 18682030603061402158010461)
              ·
                refine ⟨7005761476148025809253923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18682030603061402158010461 7005761476148025809253923)
                ·
                  refine ⟨10508642214222038713880885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7005761476148025809253923 10508642214222038713880885)
                  ·
                    refine ⟨985185207583316129426333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10508642214222038713880885 985185207583316129426333)
                    ·
                      rfl

theorem cell22_2877962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_2877962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2877962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2877962 prefixEnd_2877962 := by exact prefixLift 2877962
  have htrace : WordTrace (prefixWord ++ tailWord_2877962) baseStart_2877962 baseEnd_2877962 := by
    simpa [prefixWord, tailWord_2877962, baseEnd_2877962] using wordTrace_append hprefix tailTrace_2877962
  have hstable : (prefixWord ++ tailWord_2877962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877962).length < 2 ^ (prefixWord ++ tailWord_2877962).sum := by decide
  have hdescent : baseEnd_2877962 < baseStart_2877962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877966 : List Nat := [4, 1, 1, 2, 3, 3, 1, 2, 1, 4]
def baseStart_2877966 : Nat := 118140960795 + 2877966 * 2 ^ 59
def prefixEnd_2877966 : Nat := 4983230072969 + 3 ^ 40 * 2877966 * 2
def baseEnd_2877966 : Nat := 985186576865061452326321

theorem tailTrace_2877966 : CollatzResearch.WordTrace tailWord_2877966 prefixEnd_2877966 985186576865061452326321 := by
  unfold tailWord_2877966
  simp only [CollatzResearch.WordTrace]
  refine ⟨13121005436453521788275719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69978695661085449537470501 13121005436453521788275719)
  ·
    refine ⟨19681508154680282682413579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13121005436453521788275719 19681508154680282682413579)
    ·
      refine ⟨29522262232020424023620369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19681508154680282682413579 29522262232020424023620369)
      ·
        refine ⟨22141696674015318017715277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29522262232020424023620369 22141696674015318017715277)
        ·
          refine ⟨8303136252755744256643229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22141696674015318017715277 8303136252755744256643229)
          ·
            refine ⟨3113676094783404096241211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8303136252755744256643229 3113676094783404096241211)
            ·
              refine ⟨4670514142175106144361817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3113676094783404096241211 4670514142175106144361817)
              ·
                refine ⟨3502885606631329608271363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4670514142175106144361817 3502885606631329608271363)
                ·
                  refine ⟨5254328409946994412407045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3502885606631329608271363 5254328409946994412407045)
                  ·
                    refine ⟨985186576865061452326321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5254328409946994412407045 985186576865061452326321)
                    ·
                      rfl

theorem cell22_2877966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 2, 1, 4].length) (baseStart_2877966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2877966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2877966 prefixEnd_2877966 := by exact prefixLift 2877966
  have htrace : WordTrace (prefixWord ++ tailWord_2877966) baseStart_2877966 baseEnd_2877966 := by
    simpa [prefixWord, tailWord_2877966, baseEnd_2877966] using wordTrace_append hprefix tailTrace_2877966
  have hstable : (prefixWord ++ tailWord_2877966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877966).length < 2 ^ (prefixWord ++ tailWord_2877966).sum := by decide
  have hdescent : baseEnd_2877966 < baseStart_2877966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877992 : List Nat := [2, 1, 5, 2, 1, 11]
def baseStart_2877992 : Nat := 118140960795 + 2877992 * 2 ^ 59
def prefixEnd_2877992 : Nat := 4983230072969 + 3 ^ 40 * 2877992 * 2
def baseEnd_2877992 : Nat := 12162907125881556187361

theorem tailTrace_2877992 : CollatzResearch.WordTrace tailWord_2877992 prefixEnd_2877992 12162907125881556187361 := by
  unfold tailWord_2877992
  simp only [CollatzResearch.WordTrace]
  refine ⟨52484495894766990373326115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69979327859689320497768153 52484495894766990373326115)
  ·
    refine ⟨78726743842150485559989173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52484495894766990373326115 78726743842150485559989173)
    ·
      refine ⟨7380632235201608021248985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78726743842150485559989173 7380632235201608021248985)
      ·
        refine ⟨5535474176401206015936739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7380632235201608021248985 5535474176401206015936739)
        ·
          refine ⟨8303211264601809023905109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5535474176401206015936739 8303211264601809023905109)
          ·
            refine ⟨12162907125881556187361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8303211264601809023905109 12162907125881556187361)
            ·
              rfl

theorem cell22_2877992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 11].length) (baseStart_2877992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2877992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2877992 prefixEnd_2877992 := by exact prefixLift 2877992
  have htrace : WordTrace (prefixWord ++ tailWord_2877992) baseStart_2877992 baseEnd_2877992 := by
    simpa [prefixWord, tailWord_2877992, baseEnd_2877992] using wordTrace_append hprefix tailTrace_2877992
  have hstable : (prefixWord ++ tailWord_2877992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877992).length < 2 ^ (prefixWord ++ tailWord_2877992).sum := by decide
  have hdescent : baseEnd_2877992 < baseStart_2877992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2877994 : List Nat := [3, 1, 4, 1, 1, 2, 2, 2, 2, 4]
def baseStart_2877994 : Nat := 118140960795 + 2877994 * 2 ^ 59
def prefixEnd_2877994 : Nat := 4983230072969 + 3 ^ 40 * 2877994 * 2
def baseEnd_2877994 : Nat := 985196161837278712626235

theorem tailTrace_2877994 : CollatzResearch.WordTrace tailWord_2877994 prefixEnd_2877994 985196161837278712626235 := by
  unfold tailWord_2877994
  simp only [CollatzResearch.WordTrace]
  refine ⟨26242266183881683772056259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69979376490351156725483357 26242266183881683772056259)
  ·
    refine ⟨39363399275822525658084389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26242266183881683772056259 39363399275822525658084389)
    ·
      refine ⟨7380637364216723560890823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39363399275822525658084389 7380637364216723560890823)
      ·
        refine ⟨11070956046325085341336235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7380637364216723560890823 11070956046325085341336235)
        ·
          refine ⟨16606434069487628012004353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11070956046325085341336235 16606434069487628012004353)
          ·
            refine ⟨12454825552115721009003265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16606434069487628012004353 12454825552115721009003265)
            ·
              refine ⟨9341119164086790756752449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12454825552115721009003265 9341119164086790756752449)
              ·
                refine ⟨7005839373065093067564337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9341119164086790756752449 7005839373065093067564337)
                ·
                  refine ⟨5254379529798819800673253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7005839373065093067564337 5254379529798819800673253)
                  ·
                    refine ⟨985196161837278712626235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5254379529798819800673253 985196161837278712626235)
                    ·
                      rfl

theorem cell22_2877994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_2877994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2877994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2877994 prefixEnd_2877994 := by exact prefixLift 2877994
  have htrace : WordTrace (prefixWord ++ tailWord_2877994) baseStart_2877994 baseEnd_2877994 := by
    simpa [prefixWord, tailWord_2877994, baseEnd_2877994] using wordTrace_append hprefix tailTrace_2877994
  have hstable : (prefixWord ++ tailWord_2877994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2877994).length < 2 ^ (prefixWord ++ tailWord_2877994).sum := by decide
  have hdescent : baseEnd_2877994 < baseStart_2877994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2877994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878052 : List Nat := [2, 3, 1, 1, 2, 2, 1, 1, 4, 5]
def baseStart_2878052 : Nat := 118140960795 + 2878052 * 2 ^ 59
def prefixEnd_2878052 : Nat := 4983230072969 + 3 ^ 40 * 2878052 * 2
def baseEnd_2878052 : Nat := 985216016422585894676057

theorem tailTrace_2878052 : CollatzResearch.WordTrace tailWord_2878052 prefixEnd_2878052 985216016422585894676057 := by
  unfold tailWord_2878052
  simp only [CollatzResearch.WordTrace]
  refine ⟨52485590084658305496918205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69980786779544407329224273 52485590084658305496918205)
  ·
    refine ⟨19682096281746864561344327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52485590084658305496918205 19682096281746864561344327)
    ·
      refine ⟨29523144422620296842016491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19682096281746864561344327 29523144422620296842016491)
      ·
        refine ⟨44284716633930445263024737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29523144422620296842016491 44284716633930445263024737)
        ·
          refine ⟨33213537475447833947268553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44284716633930445263024737 33213537475447833947268553)
          ·
            refine ⟨24910153106585875460451415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33213537475447833947268553 24910153106585875460451415)
            ·
              refine ⟨37365229659878813190677123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24910153106585875460451415 37365229659878813190677123)
              ·
                refine ⟨56047844489818219786015685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37365229659878813190677123 56047844489818219786015685)
                ·
                  refine ⟨10508970841840916209877941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56047844489818219786015685 10508970841840916209877941)
                  ·
                    refine ⟨985216016422585894676057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10508970841840916209877941 985216016422585894676057)
                    ·
                      rfl

theorem cell22_2878052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_2878052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2878052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2878052 prefixEnd_2878052 := by exact prefixLift 2878052
  have htrace : WordTrace (prefixWord ++ tailWord_2878052) baseStart_2878052 baseEnd_2878052 := by
    simpa [prefixWord, tailWord_2878052, baseEnd_2878052] using wordTrace_append hprefix tailTrace_2878052
  have hstable : (prefixWord ++ tailWord_2878052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878052).length < 2 ^ (prefixWord ++ tailWord_2878052).sum := by decide
  have hdescent : baseEnd_2878052 < baseStart_2878052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878067 : List Nat := [1, 1, 1, 2, 2, 1, 1, 6, 3, 4]
def baseStart_2878067 : Nat := 118140960795 + 2878067 * 2 ^ 59
def prefixEnd_2878067 : Nat := 4983230072969 + 3 ^ 40 * 2878067 * 2
def baseEnd_2878067 : Nat := 985221151229130855551011

theorem tailTrace_2878067 : CollatzResearch.WordTrace tailWord_2878067 prefixEnd_2878067 985221151229130855551011 := by
  unfold tailWord_2878067
  simp only [CollatzResearch.WordTrace]
  refine ⟨104971727264262268555632455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69981151509508179037088303 104971727264262268555632455)
  ·
    refine ⟨157457590896393402833448683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104971727264262268555632455 157457590896393402833448683)
    ·
      refine ⟨236186386344590104250173025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157457590896393402833448683 236186386344590104250173025)
      ·
        refine ⟨177139789758442578187629769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236186386344590104250173025 177139789758442578187629769)
        ·
          refine ⟨132854842318831933640722327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177139789758442578187629769 132854842318831933640722327)
          ·
            refine ⟨199282263478247900461083491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132854842318831933640722327 199282263478247900461083491)
            ·
              refine ⟨298923395217371850691625237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199282263478247900461083491 298923395217371850691625237)
              ·
                refine ⟨14012034150814305501169933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 298923395217371850691625237 14012034150814305501169933)
                ·
                  refine ⟨5254512806555364562938725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14012034150814305501169933 5254512806555364562938725)
                  ·
                    refine ⟨985221151229130855551011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5254512806555364562938725 985221151229130855551011)
                    ·
                      rfl

theorem cell22_2878067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 3, 4].length) (baseStart_2878067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2878067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2878067 prefixEnd_2878067 := by exact prefixLift 2878067
  have htrace : WordTrace (prefixWord ++ tailWord_2878067) baseStart_2878067 baseEnd_2878067 := by
    simpa [prefixWord, tailWord_2878067, baseEnd_2878067] using wordTrace_append hprefix tailTrace_2878067
  have hstable : (prefixWord ++ tailWord_2878067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878067).length < 2 ^ (prefixWord ++ tailWord_2878067).sum := by decide
  have hdescent : baseEnd_2878067 < baseStart_2878067 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878122 : List Nat := [3, 1, 5, 2, 2, 1, 2, 1, 5]
def baseStart_2878122 : Nat := 118140960795 + 2878122 * 2 ^ 59
def prefixEnd_2878122 : Nat := 4983230072969 + 3 ^ 40 * 2878122 * 2
def baseEnd_2878122 : Nat := 328413326284376348475281

theorem tailTrace_2878122 : CollatzResearch.WordTrace tailWord_2878122 prefixEnd_2878122 328413326284376348475281 := by
  unfold tailWord_2878122
  simp only [CollatzResearch.WordTrace]
  refine ⟨26243433319765753237221155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69982488852708675299256413 26243433319765753237221155)
  ·
    refine ⟨39365149979648629855831733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26243433319765753237221155 39365149979648629855831733)
    ·
      refine ⟨3690482810592059048984225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39365149979648629855831733 3690482810592059048984225)
      ·
        refine ⟨2767862107944044286738169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3690482810592059048984225 2767862107944044286738169)
        ·
          refine ⟨2075896580958033215053627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2767862107944044286738169 2075896580958033215053627)
          ·
            refine ⟨3113844871437049822580441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2075896580958033215053627 3113844871437049822580441)
            ·
              refine ⟨2335383653577787366935331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3113844871437049822580441 2335383653577787366935331)
              ·
                refine ⟨3503075480366681050402997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2335383653577787366935331 3503075480366681050402997)
                ·
                  refine ⟨328413326284376348475281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3503075480366681050402997 328413326284376348475281)
                  ·
                    rfl

theorem cell22_2878122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 1, 5].length) (baseStart_2878122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2878122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2878122 prefixEnd_2878122 := by exact prefixLift 2878122
  have htrace : WordTrace (prefixWord ++ tailWord_2878122) baseStart_2878122 baseEnd_2878122 := by
    simpa [prefixWord, tailWord_2878122, baseEnd_2878122] using wordTrace_append hprefix tailTrace_2878122
  have hstable : (prefixWord ++ tailWord_2878122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878122).length < 2 ^ (prefixWord ++ tailWord_2878122).sum := by decide
  have hdescent : baseEnd_2878122 < baseStart_2878122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878127 : List Nat := [1, 1, 2, 1, 2, 5, 1, 9]
def baseStart_2878127 : Nat := 118140960795 + 2878127 * 2 ^ 59
def prefixEnd_2878127 : Nat := 4983230072969 + 3 ^ 40 * 2878127 * 2
def baseEnd_2878127 : Nat := 109471298939478966561203

theorem tailTrace_2878127 : CollatzResearch.WordTrace tailWord_2878127 prefixEnd_2878127 109471298939478966561203 := by
  unfold tailWord_2878127
  simp only [CollatzResearch.WordTrace]
  refine ⟨104973915644044898802816635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69982610429363265868544423 104973915644044898802816635)
  ·
    refine ⟨157460873466067348204224953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104973915644044898802816635 157460873466067348204224953)
    ·
      refine ⟨118095655099550511153168715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157460873466067348204224953 118095655099550511153168715)
      ·
        refine ⟨177143482649325766729753073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118095655099550511153168715 177143482649325766729753073)
        ·
          refine ⟨132857611986994325047314805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177143482649325766729753073 132857611986994325047314805)
          ·
            refine ⟨12455401123780717973185763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 132857611986994325047314805 12455401123780717973185763)
            ·
              refine ⟨18683101685671076959778645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12455401123780717973185763 18683101685671076959778645)
              ·
                refine ⟨109471298939478966561203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18683101685671076959778645 109471298939478966561203)
                ·
                  rfl

theorem cell22_2878127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 9].length) (baseStart_2878127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2878127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2878127 prefixEnd_2878127 := by exact prefixLift 2878127
  have htrace : WordTrace (prefixWord ++ tailWord_2878127) baseStart_2878127 baseEnd_2878127 := by
    simpa [prefixWord, tailWord_2878127, baseEnd_2878127] using wordTrace_append hprefix tailTrace_2878127
  have hstable : (prefixWord ++ tailWord_2878127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878127).length < 2 ^ (prefixWord ++ tailWord_2878127).sum := by decide
  have hdescent : baseEnd_2878127 < baseStart_2878127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878131 : List Nat := [1, 1, 1, 2, 3, 5, 1, 3, 2, 3]
def baseStart_2878131 : Nat := 118140960795 + 2878131 * 2 ^ 59
def prefixEnd_2878131 : Nat := 4983230072969 + 3 ^ 40 * 2878131 * 2
def baseEnd_2878131 : Nat := 985243059737056021950815

theorem tailTrace_2878131 : CollatzResearch.WordTrace tailWord_2878131 prefixEnd_2878131 985243059737056021950815 := by
  unfold tailWord_2878131
  simp only [CollatzResearch.WordTrace]
  refine ⟨104974061536030407485962247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69982707690686938323974831 104974061536030407485962247)
  ·
    refine ⟨157461092304045611228943371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104974061536030407485962247 157461092304045611228943371)
    ·
      refine ⟨236191638456068416843415057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157461092304045611228943371 236191638456068416843415057)
      ·
        refine ⟨177143728842051312632561293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236191638456068416843415057 177143728842051312632561293)
        ·
          refine ⟨66428898315769242237210485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177143728842051312632561293 66428898315769242237210485)
          ·
            refine ⟨6227709217103366459738483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66428898315769242237210485 6227709217103366459738483)
            ·
              refine ⟨9341563825655049689607725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6227709217103366459738483 9341563825655049689607725)
              ·
                refine ⟨3503086434620643633602897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9341563825655049689607725 3503086434620643633602897)
                ·
                  refine ⟨2627314825965482725202173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3503086434620643633602897 2627314825965482725202173)
                  ·
                    refine ⟨985243059737056021950815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2627314825965482725202173 985243059737056021950815)
                    ·
                      rfl

theorem cell22_2878131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 3, 2, 3].length) (baseStart_2878131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2878131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2878131 prefixEnd_2878131 := by exact prefixLift 2878131
  have htrace : WordTrace (prefixWord ++ tailWord_2878131) baseStart_2878131 baseEnd_2878131 := by
    simpa [prefixWord, tailWord_2878131, baseEnd_2878131] using wordTrace_append hprefix tailTrace_2878131
  have hstable : (prefixWord ++ tailWord_2878131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878131).length < 2 ^ (prefixWord ++ tailWord_2878131).sum := by decide
  have hdescent : baseEnd_2878131 < baseStart_2878131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878165 : List Nat := [1, 3, 2, 5, 1, 1, 2, 2, 2, 3]
def baseStart_2878165 : Nat := 118140960795 + 2878165 * 2 ^ 59
def prefixEnd_2878165 : Nat := 4983230072969 + 3 ^ 40 * 2878165 * 2
def baseEnd_2878165 : Nat := 985254698631891266600711

theorem tailTrace_2878165 : CollatzResearch.WordTrace tailWord_2878165 prefixEnd_2878165 985254698631891266600711 := by
  unfold tailWord_2878165
  simp only [CollatzResearch.WordTrace]
  refine ⟨104975301617907231292699949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69983534411938154195133299 104975301617907231292699949)
  ·
    refine ⟨39365738106715211734762481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104975301617907231292699949 39365738106715211734762481)
    ·
      refine ⟨29524303580036408801071861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39365738106715211734762481 29524303580036408801071861)
      ·
        refine ⟨2767903460628413325100487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29524303580036408801071861 2767903460628413325100487)
        ·
          refine ⟨4151855190942619987650731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2767903460628413325100487 4151855190942619987650731)
          ·
            refine ⟨6227782786413929981476097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4151855190942619987650731 6227782786413929981476097)
            ·
              refine ⟨4670837089810447486107073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6227782786413929981476097 4670837089810447486107073)
              ·
                refine ⟨3503127817357835614580305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4670837089810447486107073 3503127817357835614580305)
                ·
                  refine ⟨2627345863018376710935229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3503127817357835614580305 2627345863018376710935229)
                  ·
                    refine ⟨985254698631891266600711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2627345863018376710935229 985254698631891266600711)
                    ·
                      rfl

theorem cell22_2878165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 2, 2, 3].length) (baseStart_2878165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2878165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2878165 prefixEnd_2878165 := by exact prefixLift 2878165
  have htrace : WordTrace (prefixWord ++ tailWord_2878165) baseStart_2878165 baseEnd_2878165 := by
    simpa [prefixWord, tailWord_2878165, baseEnd_2878165] using wordTrace_append hprefix tailTrace_2878165
  have hstable : (prefixWord ++ tailWord_2878165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878165).length < 2 ^ (prefixWord ++ tailWord_2878165).sum := by decide
  have hdescent : baseEnd_2878165 < baseStart_2878165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878197 : List Nat := [1, 3, 6, 1, 1, 2, 1, 1, 2, 4]
def baseStart_2878197 : Nat := 118140960795 + 2878197 * 2 ^ 59
def prefixEnd_2878197 : Nat := 4983230072969 + 3 ^ 40 * 2878197 * 2
def baseEnd_2878197 : Nat := 985265652885853849800613

theorem tailTrace_2878197 : CollatzResearch.WordTrace tailWord_2878197 prefixEnd_2878197 985265652885853849800613 := by
  unfold tailWord_2878197
  simp only [CollatzResearch.WordTrace]
  refine ⟨104976468753791300757864845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69984312502527533838576563 104976468753791300757864845)
  ·
    refine ⟨39366175782671737784199317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104976468753791300757864845 39366175782671737784199317)
    ·
      refine ⟨1845289489812737708634343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 39366175782671737784199317 1845289489812737708634343)
      ·
        refine ⟨2767934234719106562951515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1845289489812737708634343 2767934234719106562951515)
        ·
          refine ⟨4151901352078659844427273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2767934234719106562951515 4151901352078659844427273)
          ·
            refine ⟨3113926014058994883320455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4151901352078659844427273 3113926014058994883320455)
            ·
              refine ⟨4670889021088492324980683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3113926014058994883320455 4670889021088492324980683)
              ·
                refine ⟨7006333531632738487471025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4670889021088492324980683 7006333531632738487471025)
                ·
                  refine ⟨5254750148724553865603269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7006333531632738487471025 5254750148724553865603269)
                  ·
                    refine ⟨985265652885853849800613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5254750148724553865603269 985265652885853849800613)
                    ·
                      rfl

theorem cell22_2878197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_2878197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2878197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2878197 prefixEnd_2878197 := by exact prefixLift 2878197
  have htrace : WordTrace (prefixWord ++ tailWord_2878197) baseStart_2878197 baseEnd_2878197 := by
    simpa [prefixWord, tailWord_2878197, baseEnd_2878197] using wordTrace_append hprefix tailTrace_2878197
  have hstable : (prefixWord ++ tailWord_2878197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878197).length < 2 ^ (prefixWord ++ tailWord_2878197).sum := by decide
  have hdescent : baseEnd_2878197 < baseStart_2878197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878210 : List Nat := [3, 4, 1, 1, 1, 2, 1, 5, 1, 3]
def baseStart_2878210 : Nat := 118140960795 + 2878210 * 2 ^ 59
def prefixEnd_2878210 : Nat := 4983230072969 + 3 ^ 40 * 2878210 * 2
def baseEnd_2878210 : Nat := 985270103051526149225573

theorem tailTrace_2878210 : CollatzResearch.WordTrace tailWord_2878210 prefixEnd_2878210 985270103051526149225573 := by
  unfold tailWord_2878210
  simp only [CollatzResearch.WordTrace]
  refine ⟨26244235725686050994522021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69984628601829469318725389 26244235725686050994522021)
  ·
    refine ⟨4920794198566134561472879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26244235725686050994522021 4920794198566134561472879)
    ·
      refine ⟨7381191297849201842209319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4920794198566134561472879 7381191297849201842209319)
      ·
        refine ⟨11071786946773802763313979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7381191297849201842209319 11071786946773802763313979)
        ·
          refine ⟨16607680420160704144970969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11071786946773802763313979 16607680420160704144970969)
          ·
            refine ⟨12455760315120528108728227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16607680420160704144970969 12455760315120528108728227)
            ·
              refine ⟨18683640472680792163092341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12455760315120528108728227 18683640472680792163092341)
              ·
                refine ⟨1751591294313824265289907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18683640472680792163092341 1751591294313824265289907)
                ·
                  refine ⟨2627386941470736397934861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1751591294313824265289907 2627386941470736397934861)
                  ·
                    refine ⟨985270103051526149225573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2627386941470736397934861 985270103051526149225573)
                    ·
                      rfl

theorem cell22_2878210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_2878210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2878210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2878210 prefixEnd_2878210 := by exact prefixLift 2878210
  have htrace : WordTrace (prefixWord ++ tailWord_2878210) baseStart_2878210 baseEnd_2878210 := by
    simpa [prefixWord, tailWord_2878210, baseEnd_2878210] using wordTrace_append hprefix tailTrace_2878210
  have hstable : (prefixWord ++ tailWord_2878210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878210).length < 2 ^ (prefixWord ++ tailWord_2878210).sum := by decide
  have hdescent : baseEnd_2878210 < baseStart_2878210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878264 : List Nat := [2, 1, 2, 1, 3, 2, 1, 3, 1, 6]
def baseStart_2878264 : Nat := 118140960795 + 2878264 * 2 ^ 59
def prefixEnd_2878264 : Nat := 4983230072969 + 3 ^ 40 * 2878264 * 2
def baseEnd_2878264 : Nat := 985288588355088008375407

theorem tailTrace_2878264 : CollatzResearch.WordTrace tailWord_2878264 prefixEnd_2878264 985288588355088008375407 := by
  unfold tailWord_2878264
  simp only [CollatzResearch.WordTrace]
  refine ⟨52489456222274285600276923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69985941629699047467035897 52489456222274285600276923)
  ·
    refine ⟨78734184333411428400415385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52489456222274285600276923 78734184333411428400415385)
    ·
      refine ⟨59050638250058571300311539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78734184333411428400415385 59050638250058571300311539)
      ·
        refine ⟨88575957375087856950467309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59050638250058571300311539 88575957375087856950467309)
        ·
          refine ⟨33215984015657946356425241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88575957375087856950467309 33215984015657946356425241)
          ·
            refine ⟨24911988011743459767318931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33215984015657946356425241 24911988011743459767318931)
            ·
              refine ⟨37367982017615189650978397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24911988011743459767318931 37367982017615189650978397)
              ·
                refine ⟨14012993256605696119116899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37367982017615189650978397 14012993256605696119116899)
                ·
                  refine ⟨21019489884908544178675349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14012993256605696119116899 21019489884908544178675349)
                  ·
                    refine ⟨985288588355088008375407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21019489884908544178675349 985288588355088008375407)
                    ·
                      rfl

theorem cell22_2878264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 1, 6].length) (baseStart_2878264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2878264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2878264 prefixEnd_2878264 := by exact prefixLift 2878264
  have htrace : WordTrace (prefixWord ++ tailWord_2878264) baseStart_2878264 baseEnd_2878264 := by
    simpa [prefixWord, tailWord_2878264, baseEnd_2878264] using wordTrace_append hprefix tailTrace_2878264
  have hstable : (prefixWord ++ tailWord_2878264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878264).length < 2 ^ (prefixWord ++ tailWord_2878264).sum := by decide
  have hdescent : baseEnd_2878264 < baseStart_2878264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878281 : List Nat := [1, 2, 1, 1, 2, 6, 1, 2, 2, 4]
def baseStart_2878281 : Nat := 118140960795 + 2878281 * 2 ^ 59
def prefixEnd_2878281 : Nat := 4983230072969 + 3 ^ 40 * 2878281 * 2
def baseEnd_2878281 : Nat := 985294407802505630700355

theorem tailTrace_2878281 : CollatzResearch.WordTrace tailWord_2878281 prefixEnd_2878281 985294407802505630700355 := by
  unfold tailWord_2878281
  simp only [CollatzResearch.WordTrace]
  refine ⟨104979532485486983103922697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69986354990324655402615131 104979532485486983103922697)
  ·
    refine ⟨78734649364115237327942023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104979532485486983103922697 78734649364115237327942023)
    ·
      refine ⟨118101974046172855991913035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78734649364115237327942023 118101974046172855991913035)
      ·
        refine ⟨177152961069259283987869553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118101974046172855991913035 177152961069259283987869553)
        ·
          refine ⟨132864720801944462990902165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177152961069259283987869553 132864720801944462990902165)
          ·
            refine ⟨6228033787591146702698539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 132864720801944462990902165 6228033787591146702698539)
            ·
              refine ⟨9342050681386720054047809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6228033787591146702698539 9342050681386720054047809)
              ·
                refine ⟨7006538011040040040535857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9342050681386720054047809 7006538011040040040535857)
                ·
                  refine ⟨5254903508280030030401893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7006538011040040040535857 5254903508280030030401893)
                  ·
                    refine ⟨985294407802505630700355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5254903508280030030401893 985294407802505630700355)
                    ·
                      rfl

theorem cell22_2878281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 2, 4].length) (baseStart_2878281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2878281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2878281 prefixEnd_2878281 := by exact prefixLift 2878281
  have htrace : WordTrace (prefixWord ++ tailWord_2878281) baseStart_2878281 baseEnd_2878281 := by
    simpa [prefixWord, tailWord_2878281, baseEnd_2878281] using wordTrace_append hprefix tailTrace_2878281
  have hstable : (prefixWord ++ tailWord_2878281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878281).length < 2 ^ (prefixWord ++ tailWord_2878281).sum := by decide
  have hdescent : baseEnd_2878281 < baseStart_2878281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878285 : List Nat := [1, 6, 1, 2, 2, 2, 1, 1, 6]
def baseStart_2878285 : Nat := 118140960795 + 2878285 * 2 ^ 59
def prefixEnd_2878285 : Nat := 4983230072969 + 3 ^ 40 * 2878285 * 2
def baseEnd_2878285 : Nat := 328431925694750317866781

theorem tailTrace_2878285 : CollatzResearch.WordTrace tailWord_2878285 prefixEnd_2878285 328431925694750317866781 := by
  unfold tailWord_2878285
  simp only [CollatzResearch.WordTrace]
  refine ⟨104979678377472491787068309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69986452251648327858045539 104979678377472491787068309)
  ·
    refine ⟨4920922423944023052518827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 104979678377472491787068309 4920922423944023052518827)
    ·
      refine ⟨7381383635916034578778241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4920922423944023052518827 7381383635916034578778241)
      ·
        refine ⟨5536037726937025934083681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7381383635916034578778241 5536037726937025934083681)
        ·
          refine ⟨4152028295202769450562761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5536037726937025934083681 4152028295202769450562761)
          ·
            refine ⟨3114021221402077087922071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4152028295202769450562761 3114021221402077087922071)
            ·
              refine ⟨4671031832103115631883107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3114021221402077087922071 4671031832103115631883107)
              ·
                refine ⟨7006547748154673447824661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4671031832103115631883107 7006547748154673447824661)
                ·
                  refine ⟨328431925694750317866781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7006547748154673447824661 328431925694750317866781)
                  ·
                    rfl

theorem cell22_2878285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_2878285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2878285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2878285 prefixEnd_2878285 := by exact prefixLift 2878285
  have htrace : WordTrace (prefixWord ++ tailWord_2878285) baseStart_2878285 baseEnd_2878285 := by
    simpa [prefixWord, tailWord_2878285, baseEnd_2878285] using wordTrace_append hprefix tailTrace_2878285
  have hstable : (prefixWord ++ tailWord_2878285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878285).length < 2 ^ (prefixWord ++ tailWord_2878285).sum := by decide
  have hdescent : baseEnd_2878285 < baseStart_2878285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878300 : List Nat := [2, 2, 4, 2, 1, 2, 1, 3, 2, 3]
def baseStart_2878300 : Nat := 118140960795 + 2878300 * 2 ^ 59
def prefixEnd_2878300 : Nat := 4983230072969 + 3 ^ 40 * 2878300 * 2
def baseEnd_2878300 : Nat := 985300911890795914475297

theorem tailTrace_2878300 : CollatzResearch.WordTrace tailWord_2878300 prefixEnd_2878300 985300911890795914475297 := by
  unfold tailWord_2878300
  simp only [CollatzResearch.WordTrace]
  refine ⟨52490112736209074674432177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69986816981612099565909569 52490112736209074674432177)
  ·
    refine ⟨39367584552156806005824133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52490112736209074674432177 39367584552156806005824133)
    ·
      refine ⟨7381422103529401126092025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39367584552156806005824133 7381422103529401126092025)
      ·
        refine ⟨5536066577647050844569019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7381422103529401126092025 5536066577647050844569019)
        ·
          refine ⟨8304099866470576266853529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5536066577647050844569019 8304099866470576266853529)
          ·
            refine ⟨6228074899852932200140147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8304099866470576266853529 6228074899852932200140147)
            ·
              refine ⟨9342112349779398300210221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6228074899852932200140147 9342112349779398300210221)
              ·
                refine ⟨3503292131167274362578833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9342112349779398300210221 3503292131167274362578833)
                ·
                  refine ⟨2627469098375455771934125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3503292131167274362578833 2627469098375455771934125)
                  ·
                    refine ⟨985300911890795914475297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2627469098375455771934125 985300911890795914475297)
                    ·
                      rfl

theorem cell22_2878300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_2878300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2878300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2878300 prefixEnd_2878300 := by exact prefixLift 2878300
  have htrace : WordTrace (prefixWord ++ tailWord_2878300) baseStart_2878300 baseEnd_2878300 := by
    simpa [prefixWord, tailWord_2878300, baseEnd_2878300] using wordTrace_append hprefix tailTrace_2878300
  have hstable : (prefixWord ++ tailWord_2878300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878300).length < 2 ^ (prefixWord ++ tailWord_2878300).sum := by decide
  have hdescent : baseEnd_2878300 < baseStart_2878300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878341 : List Nat := [1, 3, 1, 1, 3, 3, 1, 4, 5]
def baseStart_2878341 : Nat := 118140960795 + 2878341 * 2 ^ 59
def prefixEnd_2878341 : Nat := 4983230072969 + 3 ^ 40 * 2878341 * 2
def baseEnd_2878341 : Nat := 328438315676228491400057

theorem tailTrace_2878341 : CollatzResearch.WordTrace tailWord_2878341 prefixEnd_2878341 328438315676228491400057 := by
  unfold tailWord_2878341
  simp only [CollatzResearch.WordTrace]
  refine ⟨104981720865269613351106877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69987813910179742234071251 104981720865269613351106877)
  ·
    refine ⟨39368145324476105006665079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104981720865269613351106877 39368145324476105006665079)
    ·
      refine ⟨59052217986714157509997619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39368145324476105006665079 59052217986714157509997619)
      ·
        refine ⟨88578326980071236264996429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59052217986714157509997619 88578326980071236264996429)
        ·
          refine ⟨33216872617526713599373661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88578326980071236264996429 33216872617526713599373661)
          ·
            refine ⟨12456327231572517599765123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33216872617526713599373661 12456327231572517599765123)
            ·
              refine ⟨18684490847358776399647685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12456327231572517599765123 18684490847358776399647685)
              ·
                refine ⟨3503342033879770574933941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18684490847358776399647685 3503342033879770574933941)
                ·
                  refine ⟨328438315676228491400057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3503342033879770574933941 328438315676228491400057)
                  ·
                    rfl

theorem cell22_2878341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 4, 5].length) (baseStart_2878341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2878341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2878341 prefixEnd_2878341 := by exact prefixLift 2878341
  have htrace : WordTrace (prefixWord ++ tailWord_2878341) baseStart_2878341 baseEnd_2878341 := by
    simpa [prefixWord, tailWord_2878341, baseEnd_2878341] using wordTrace_append hprefix tailTrace_2878341
  have hstable : (prefixWord ++ tailWord_2878341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878341).length < 2 ^ (prefixWord ++ tailWord_2878341).sum := by decide
  have hdescent : baseEnd_2878341 < baseStart_2878341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878345 : List Nat := [1, 2, 1, 1, 5, 3, 1, 4, 1, 3]
def baseStart_2878345 : Nat := 118140960795 + 2878345 * 2 ^ 59
def prefixEnd_2878345 : Nat := 4983230072969 + 3 ^ 40 * 2878345 * 2
def baseEnd_2878345 : Nat := 985316316310430797100159

theorem tailTrace_2878345 : CollatzResearch.WordTrace tailWord_2878345 prefixEnd_2878345 985316316310430797100159 := by
  unfold tailWord_2878345
  simp only [CollatzResearch.WordTrace]
  refine ⟨104981866757255122034252489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69987911171503414689501659 104981866757255122034252489)
  ·
    refine ⟨78736400067941341525689367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104981866757255122034252489 78736400067941341525689367)
    ·
      refine ⟨118104600101912012288534051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78736400067941341525689367 118104600101912012288534051)
      ·
        refine ⟨177156900152868018432801077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118104600101912012288534051 177156900152868018432801077)
        ·
          refine ⟨16608459389331376728075101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 177156900152868018432801077 16608459389331376728075101)
          ·
            refine ⟨6228172270999266273028163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16608459389331376728075101 6228172270999266273028163)
            ·
              refine ⟨9342258406498899409542245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6228172270999266273028163 9342258406498899409542245)
              ·
                refine ⟨1751673451218543639289171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9342258406498899409542245 1751673451218543639289171)
                ·
                  refine ⟨2627510176827815458933757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1751673451218543639289171 2627510176827815458933757)
                  ·
                    refine ⟨985316316310430797100159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2627510176827815458933757 985316316310430797100159)
                    ·
                      rfl

theorem cell22_2878345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 4, 1, 3].length) (baseStart_2878345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2878345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2878345 prefixEnd_2878345 := by exact prefixLift 2878345
  have htrace : WordTrace (prefixWord ++ tailWord_2878345) baseStart_2878345 baseEnd_2878345 := by
    simpa [prefixWord, tailWord_2878345, baseEnd_2878345] using wordTrace_append hprefix tailTrace_2878345
  have hstable : (prefixWord ++ tailWord_2878345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878345).length < 2 ^ (prefixWord ++ tailWord_2878345).sum := by decide
  have hdescent : baseEnd_2878345 < baseStart_2878345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878371 : List Nat := [1, 1, 1, 4, 1, 2, 4, 1, 3, 4]
def baseStart_2878371 : Nat := 118140960795 + 2878371 * 2 ^ 59
def prefixEnd_2878371 : Nat := 4983230072969 + 3 ^ 40 * 2878371 * 2
def baseEnd_2878371 : Nat := 985325216641775395950079

theorem tailTrace_2878371 : CollatzResearch.WordTrace tailWord_2878371 prefixEnd_2878371 985325216641775395950079 := by
  unfold tailWord_2878371
  simp only [CollatzResearch.WordTrace]
  refine ⟨104982815055160928474698967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69988543370107285649799311 104982815055160928474698967)
  ·
    refine ⟨157474222582741392712048451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104982815055160928474698967 157474222582741392712048451)
    ·
      refine ⟨236211333874112089068072677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157474222582741392712048451 236211333874112089068072677)
      ·
        refine ⟨44289625101396016700263627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 236211333874112089068072677 44289625101396016700263627)
        ·
          refine ⟨66434437652094025050395441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44289625101396016700263627 66434437652094025050395441)
          ·
            refine ⟨49825828239070518787796581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66434437652094025050395441 49825828239070518787796581)
            ·
              refine ⟨9342342794825722272711859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49825828239070518787796581 9342342794825722272711859)
              ·
                refine ⟨14013514192238583409067789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9342342794825722272711859 14013514192238583409067789)
                ·
                  refine ⟨5255067822089468778400421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14013514192238583409067789 5255067822089468778400421)
                  ·
                    refine ⟨985325216641775395950079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5255067822089468778400421 985325216641775395950079)
                    ·
                      rfl

theorem cell22_2878371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 3, 4].length) (baseStart_2878371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2878371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2878371 prefixEnd_2878371 := by exact prefixLift 2878371
  have htrace : WordTrace (prefixWord ++ tailWord_2878371) baseStart_2878371 baseEnd_2878371 := by
    simpa [prefixWord, tailWord_2878371, baseEnd_2878371] using wordTrace_append hprefix tailTrace_2878371
  have hstable : (prefixWord ++ tailWord_2878371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878371).length < 2 ^ (prefixWord ++ tailWord_2878371).sum := by decide
  have hdescent : baseEnd_2878371 < baseStart_2878371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878422 : List Nat := [5, 2, 1, 1, 2, 2, 2, 2, 1, 4]
def baseStart_2878422 : Nat := 118140960795 + 2878422 * 2 ^ 59
def prefixEnd_2878422 : Nat := 4983230072969 + 3 ^ 40 * 2878422 * 2
def baseEnd_2878422 : Nat := 985342674984028262924923

theorem tailTrace_2878422 : CollatzResearch.WordTrace tailWord_2878422 prefixEnd_2878422 985342674984028262924923 := by
  unfold tailWord_2878422
  simp only [CollatzResearch.WordTrace]
  refine ⟨6561542198623510261550345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69989783451984109456537013 6561542198623510261550345)
  ·
    refine ⟨4921156648967632696162759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6561542198623510261550345 4921156648967632696162759)
    ·
      refine ⟨7381734973451449044244139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4921156648967632696162759 7381734973451449044244139)
      ·
        refine ⟨11072602460177173566366209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7381734973451449044244139 11072602460177173566366209)
        ·
          refine ⟨8304451845132880174774657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11072602460177173566366209 8304451845132880174774657)
          ·
            refine ⟨6228338883849660131080993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8304451845132880174774657 6228338883849660131080993)
            ·
              refine ⟨4671254162887245098310745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6228338883849660131080993 4671254162887245098310745)
              ·
                refine ⟨3503440622165433823733059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4671254162887245098310745 3503440622165433823733059)
                ·
                  refine ⟨5255160933248150735599589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3503440622165433823733059 5255160933248150735599589)
                  ·
                    refine ⟨985342674984028262924923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5255160933248150735599589 985342674984028262924923)
                    ·
                      rfl

theorem cell22_2878422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_2878422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2878422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2878422 prefixEnd_2878422 := by exact prefixLift 2878422
  have htrace : WordTrace (prefixWord ++ tailWord_2878422) baseStart_2878422 baseEnd_2878422 := by
    simpa [prefixWord, tailWord_2878422, baseEnd_2878422] using wordTrace_append hprefix tailTrace_2878422
  have hstable : (prefixWord ++ tailWord_2878422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878422).length < 2 ^ (prefixWord ++ tailWord_2878422).sum := by decide
  have hdescent : baseEnd_2878422 < baseStart_2878422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878461 : List Nat := [1, 4, 1, 1, 1, 2, 1, 3, 2, 6]
def baseStart_2878461 : Nat := 118140960795 + 2878461 * 2 ^ 59
def prefixEnd_2878461 : Nat := 4983230072969 + 3 ^ 40 * 2878461 * 2
def baseEnd_2878461 : Nat := 985356025481045161199803

theorem tailTrace_2878461 : CollatzResearch.WordTrace tailWord_2878461 prefixEnd_2878461 985356025481045161199803 := by
  unfold tailWord_2878461
  simp only [CollatzResearch.WordTrace]
  refine ⟨104986097624834873845475237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69990731749889915896983491 104986097624834873845475237)
  ·
    refine ⟨19684893304656538846026607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104986097624834873845475237 19684893304656538846026607)
    ·
      refine ⟨29527339956984808269039911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19684893304656538846026607 29527339956984808269039911)
      ·
        refine ⟨44291009935477212403559867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29527339956984808269039911 44291009935477212403559867)
        ·
          refine ⟨66436514903215818605339801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44291009935477212403559867 66436514903215818605339801)
          ·
            refine ⟨49827386177411863954004851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66436514903215818605339801 49827386177411863954004851)
            ·
              refine ⟨74741079266117795931007277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49827386177411863954004851 74741079266117795931007277)
              ·
                refine ⟨28027904724794173474127729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74741079266117795931007277 28027904724794173474127729)
                ·
                  refine ⟨21020928543595630105595797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28027904724794173474127729 21020928543595630105595797)
                  ·
                    refine ⟨985356025481045161199803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21020928543595630105595797 985356025481045161199803)
                    ·
                      rfl

theorem cell22_2878461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_2878461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2878461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2878461 prefixEnd_2878461 := by exact prefixLift 2878461
  have htrace : WordTrace (prefixWord ++ tailWord_2878461) baseStart_2878461 baseEnd_2878461 := by
    simpa [prefixWord, tailWord_2878461, baseEnd_2878461] using wordTrace_append hprefix tailTrace_2878461
  have hstable : (prefixWord ++ tailWord_2878461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878461).length < 2 ^ (prefixWord ++ tailWord_2878461).sum := by decide
  have hdescent : baseEnd_2878461 < baseStart_2878461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878510 : List Nat := [4, 1, 3, 1, 1, 1, 4, 2, 5]
def baseStart_2878510 : Nat := 118140960795 + 2878510 * 2 ^ 59
def prefixEnd_2878510 : Nat := 4983230072969 + 3 ^ 40 * 2878510 * 2
def baseEnd_2878510 : Nat := 328457599727475122241551

theorem tailTrace_2878510 : CollatzResearch.WordTrace tailWord_2878510 prefixEnd_2878510 328457599727475122241551 := by
  unfold tailWord_2878510
  simp only [CollatzResearch.WordTrace]
  refine ⟨13123485600207169401751123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69991923201104903476005989 13123485600207169401751123)
  ·
    refine ⟨19685228400310754102626685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13123485600207169401751123 19685228400310754102626685)
    ·
      refine ⟨7381960650116532788485007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19685228400310754102626685 7381960650116532788485007)
      ·
        refine ⟨11072940975174799182727511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7381960650116532788485007 11072940975174799182727511)
        ·
          refine ⟨16609411462762198774091267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11072940975174799182727511 16609411462762198774091267)
          ·
            refine ⟨24914117194143298161136901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16609411462762198774091267 24914117194143298161136901)
            ·
              refine ⟨4671396973901868405213169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24914117194143298161136901 4671396973901868405213169)
              ·
                refine ⟨3503547730426401303909877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4671396973901868405213169 3503547730426401303909877)
                ·
                  refine ⟨328457599727475122241551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3503547730426401303909877 328457599727475122241551)
                  ·
                    rfl

theorem cell22_2878510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 2, 5].length) (baseStart_2878510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2878510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2878510 prefixEnd_2878510 := by exact prefixLift 2878510
  have htrace : WordTrace (prefixWord ++ tailWord_2878510) baseStart_2878510 baseEnd_2878510 := by
    simpa [prefixWord, tailWord_2878510, baseEnd_2878510] using wordTrace_append hprefix tailTrace_2878510
  have hstable : (prefixWord ++ tailWord_2878510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878510).length < 2 ^ (prefixWord ++ tailWord_2878510).sum := by decide
  have hdescent : baseEnd_2878510 < baseStart_2878510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878600 : List Nat := [2, 1, 3, 4, 2, 1, 1, 8]
def baseStart_2878600 : Nat := 118140960795 + 2878600 * 2 ^ 59
def prefixEnd_2878600 : Nat := 4983230072969 + 3 ^ 40 * 2878600 * 2
def baseEnd_2878600 : Nat := 109489289780188347997153

theorem tailTrace_2878600 : CollatzResearch.WordTrace tailWord_2878600 prefixEnd_2878600 109489289780188347997153 := by
  unfold tailWord_2878600
  simp only [CollatzResearch.WordTrace]
  refine ⟨52495583685665650292392627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69994111580887533723190169 52495583685665650292392627)
  ·
    refine ⟨78743375528498475438588941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52495583685665650292392627 78743375528498475438588941)
    ·
      refine ⟨29528765823186928289470853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78743375528498475438588941 29528765823186928289470853)
      ·
        refine ⟨5536643591847549054275785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29528765823186928289470853 5536643591847549054275785)
        ·
          refine ⟨4152482693885661790706839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5536643591847549054275785 4152482693885661790706839)
          ·
            refine ⟨6228724040828492686060259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4152482693885661790706839 6228724040828492686060259)
            ·
              refine ⟨9343086061242739029090389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6228724040828492686060259 9343086061242739029090389)
              ·
                refine ⟨109489289780188347997153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9343086061242739029090389 109489289780188347997153)
                ·
                  rfl

theorem cell22_2878600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 8].length) (baseStart_2878600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2878600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2878600 prefixEnd_2878600 := by exact prefixLift 2878600
  have htrace : WordTrace (prefixWord ++ tailWord_2878600) baseStart_2878600 baseEnd_2878600 := by
    simpa [prefixWord, tailWord_2878600, baseEnd_2878600] using wordTrace_append hprefix tailTrace_2878600
  have hstable : (prefixWord ++ tailWord_2878600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878600).length < 2 ^ (prefixWord ++ tailWord_2878600).sum := by decide
  have hdescent : baseEnd_2878600 < baseStart_2878600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878643 : List Nat := [1, 1, 1, 2, 3, 2, 2, 3, 2, 5]
def baseStart_2878643 : Nat := 118140960795 + 2878643 * 2 ^ 59
def prefixEnd_2878643 : Nat := 4983230072969 + 3 ^ 40 * 2878643 * 2
def baseEnd_2878643 : Nat := 985418327800457353149245

theorem tailTrace_2878643 : CollatzResearch.WordTrace tailWord_2878643 prefixEnd_2878643 985418327800457353149245 := by
  unfold tailWord_2878643
  simp only [CollatzResearch.WordTrace]
  refine ⟨104992735710175518928600583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69995157140117012619067055 104992735710175518928600583)
  ·
    refine ⟨157489103565263278392900875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104992735710175518928600583 157489103565263278392900875)
    ·
      refine ⟨236233655347894917589351313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157489103565263278392900875 236233655347894917589351313)
      ·
        refine ⟨177175241510921188192013485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236233655347894917589351313 177175241510921188192013485)
        ·
          refine ⟨66440715566595445572005057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177175241510921188192013485 66440715566595445572005057)
          ·
            refine ⟨49830536674946584179003793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66440715566595445572005057 49830536674946584179003793)
            ·
              refine ⟨37372902506209938134252845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49830536674946584179003793 37372902506209938134252845)
              ·
                refine ⟨14014838439828726800344817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37372902506209938134252845 14014838439828726800344817)
                ·
                  refine ⟨10511128829871545100258613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14014838439828726800344817 10511128829871545100258613)
                  ·
                    refine ⟨985418327800457353149245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10511128829871545100258613 985418327800457353149245)
                    ·
                      rfl

theorem cell22_2878643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 5].length) (baseStart_2878643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2878643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2878643 prefixEnd_2878643 := by exact prefixLift 2878643
  have htrace : WordTrace (prefixWord ++ tailWord_2878643) baseStart_2878643 baseEnd_2878643 := by
    simpa [prefixWord, tailWord_2878643, baseEnd_2878643] using wordTrace_append hprefix tailTrace_2878643
  have hstable : (prefixWord ++ tailWord_2878643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878643).length < 2 ^ (prefixWord ++ tailWord_2878643).sum := by decide
  have hdescent : baseEnd_2878643 < baseStart_2878643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878705 : List Nat := [1, 2, 2, 2, 2, 1, 1, 2, 6, 3]
def baseStart_2878705 : Nat := 118140960795 + 2878705 * 2 ^ 59
def prefixEnd_2878705 : Nat := 4983230072969 + 3 ^ 40 * 2878705 * 2
def baseEnd_2878705 : Nat := 985439551667509858099055

theorem tailTrace_2878705 : CollatzResearch.WordTrace tailWord_2878705 prefixEnd_2878705 985439551667509858099055 := by
  unfold tailWord_2878705
  simp only [CollatzResearch.WordTrace]
  refine ⟨104994997035950903517357569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69996664690633935678238379 104994997035950903517357569)
  ·
    refine ⟨78746247776963177638018177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104994997035950903517357569 78746247776963177638018177)
    ·
      refine ⟨59059685832722383228513633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78746247776963177638018177 59059685832722383228513633)
      ·
        refine ⟨44294764374541787421385225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59059685832722383228513633 44294764374541787421385225)
        ·
          refine ⟨33221073280906340566038919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44294764374541787421385225 33221073280906340566038919)
          ·
            refine ⟨49831609921359510849058379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33221073280906340566038919 49831609921359510849058379)
            ·
              refine ⟨74747414882039266273587569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49831609921359510849058379 74747414882039266273587569)
              ·
                refine ⟨56060561161529449705190677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74747414882039266273587569 56060561161529449705190677)
                ·
                  refine ⟨2627838804446692954930813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 56060561161529449705190677 2627838804446692954930813)
                  ·
                    refine ⟨985439551667509858099055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2627838804446692954930813 985439551667509858099055)
                    ·
                      rfl

theorem cell22_2878705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 6, 3].length) (baseStart_2878705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2878705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2878705 prefixEnd_2878705 := by exact prefixLift 2878705
  have htrace : WordTrace (prefixWord ++ tailWord_2878705) baseStart_2878705 baseEnd_2878705 := by
    simpa [prefixWord, tailWord_2878705, baseEnd_2878705] using wordTrace_append hprefix tailTrace_2878705
  have hstable : (prefixWord ++ tailWord_2878705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878705).length < 2 ^ (prefixWord ++ tailWord_2878705).sum := by decide
  have hdescent : baseEnd_2878705 < baseStart_2878705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878724 : List Nat := [2, 3, 2, 2, 2, 2, 2, 3, 4]
def baseStart_2878724 : Nat := 118140960795 + 2878724 * 2 ^ 59
def prefixEnd_2878724 : Nat := 4983230072969 + 3 ^ 40 * 2878724 * 2
def baseEnd_2878724 : Nat := 328482018585266713957999

theorem tailTrace_2878724 : CollatzResearch.WordTrace tailWord_2878724 prefixEnd_2878724 328482018585266713957999 := by
  unfold tailWord_2878724
  simp only [CollatzResearch.WordTrace]
  refine ⟨52497845011441034881149613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69997126681921379841532817 52497845011441034881149613)
  ·
    refine ⟨19686691879290388080431105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52497845011441034881149613 19686691879290388080431105)
    ·
      refine ⟨14765018909467791060323329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19686691879290388080431105 14765018909467791060323329)
      ·
        refine ⟨11073764182100843295242497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14765018909467791060323329 11073764182100843295242497)
        ·
          refine ⟨8305323136575632471431873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11073764182100843295242497 8305323136575632471431873)
          ·
            refine ⟨6228992352431724353573905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8305323136575632471431873 6228992352431724353573905)
            ·
              refine ⟨4671744264323793265180429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6228992352431724353573905 4671744264323793265180429)
              ·
                refine ⟨1751904099121422474442661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4671744264323793265180429 1751904099121422474442661)
                ·
                  refine ⟨328482018585266713957999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1751904099121422474442661 328482018585266713957999)
                  ·
                    rfl

theorem cell22_2878724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 3, 4].length) (baseStart_2878724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2878724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2878724 prefixEnd_2878724 := by exact prefixLift 2878724
  have htrace : WordTrace (prefixWord ++ tailWord_2878724) baseStart_2878724 baseEnd_2878724 := by
    simpa [prefixWord, tailWord_2878724, baseEnd_2878724] using wordTrace_append hprefix tailTrace_2878724
  have hstable : (prefixWord ++ tailWord_2878724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878724).length < 2 ^ (prefixWord ++ tailWord_2878724).sum := by decide
  have hdescent : baseEnd_2878724 < baseStart_2878724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878780 : List Nat := [2, 2, 2, 2, 1, 3, 1, 2, 7]
def baseStart_2878780 : Nat := 118140960795 + 2878780 * 2 ^ 59
def prefixEnd_2878780 : Nat := 4983230072969 + 3 ^ 40 * 2878780 * 2
def baseEnd_2878780 : Nat := 328488408566744887491275

theorem tailTrace_2878780 : CollatzResearch.WordTrace tailWord_2878780 prefixEnd_2878780 328488408566744887491275 := by
  unfold tailWord_2878780
  simp only [CollatzResearch.WordTrace]
  refine ⟨52498866255339595663168897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69998488340452794217558529 52498866255339595663168897)
  ·
    refine ⟨39374149691504696747376673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52498866255339595663168897 39374149691504696747376673)
    ·
      refine ⟨29530612268628522560532505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39374149691504696747376673 29530612268628522560532505)
      ·
        refine ⟨22147959201471391920399379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29530612268628522560532505 22147959201471391920399379)
        ·
          refine ⟨33221938802207087880599069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22147959201471391920399379 33221938802207087880599069)
          ·
            refine ⟨12458227050827657955224651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33221938802207087880599069 12458227050827657955224651)
            ·
              refine ⟨18687340576241486932836977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12458227050827657955224651 18687340576241486932836977)
              ·
                refine ⟨14015505432181115199627733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18687340576241486932836977 14015505432181115199627733)
                ·
                  refine ⟨328488408566744887491275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14015505432181115199627733 328488408566744887491275)
                  ·
                    rfl

theorem cell22_2878780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 7].length) (baseStart_2878780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2878780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2878780 prefixEnd_2878780 := by exact prefixLift 2878780
  have htrace : WordTrace (prefixWord ++ tailWord_2878780) baseStart_2878780 baseEnd_2878780 := by
    simpa [prefixWord, tailWord_2878780, baseEnd_2878780] using wordTrace_append hprefix tailTrace_2878780
  have hstable : (prefixWord ++ tailWord_2878780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878780).length < 2 ^ (prefixWord ++ tailWord_2878780).sum := by decide
  have hdescent : baseEnd_2878780 < baseStart_2878780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878801 : List Nat := [1, 2, 2, 1, 4, 1, 5, 2, 1, 3]
def baseStart_2878801 : Nat := 118140960795 + 2878801 * 2 ^ 59
def prefixEnd_2878801 : Nat := 4983230072969 + 3 ^ 40 * 2878801 * 2
def baseEnd_2878801 : Nat := 985472414429397607698761

theorem tailTrace_2878801 : CollatzResearch.WordTrace tailWord_2878801 prefixEnd_2878801 985472414429397607698761 := by
  unfold tailWord_2878801
  simp only [CollatzResearch.WordTrace]
  refine ⟨104998498443603111912852257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69998998962402074608568171 104998498443603111912852257)
  ·
    refine ⟨78748873832702333934639193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104998498443603111912852257 78748873832702333934639193)
    ·
      refine ⟨59061655374526750450979395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78748873832702333934639193 59061655374526750450979395)
      ·
        refine ⟨88592483061790125676469093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59061655374526750450979395 88592483061790125676469093)
        ·
          refine ⟨16611090574085648564337955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88592483061790125676469093 16611090574085648564337955)
          ·
            refine ⟨24916635861128472846506933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16611090574085648564337955 24916635861128472846506933)
            ·
              refine ⟨2335934611980794329360025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24916635861128472846506933 2335934611980794329360025)
              ·
                refine ⟨1751950958985595747020019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2335934611980794329360025 1751950958985595747020019)
                ·
                  refine ⟨2627926438478393620530029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1751950958985595747020019 2627926438478393620530029)
                  ·
                    refine ⟨985472414429397607698761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2627926438478393620530029 985472414429397607698761)
                    ·
                      rfl

theorem cell22_2878801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 2, 1, 3].length) (baseStart_2878801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2878801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2878801 prefixEnd_2878801 := by exact prefixLift 2878801
  have htrace : WordTrace (prefixWord ++ tailWord_2878801) baseStart_2878801 baseEnd_2878801 := by
    simpa [prefixWord, tailWord_2878801, baseEnd_2878801] using wordTrace_append hprefix tailTrace_2878801
  have hstable : (prefixWord ++ tailWord_2878801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878801).length < 2 ^ (prefixWord ++ tailWord_2878801).sum := by decide
  have hdescent : baseEnd_2878801 < baseStart_2878801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878844 : List Nat := [2, 2, 2, 1, 1, 1, 7, 1, 1, 4]
def baseStart_2878844 : Nat := 118140960795 + 2878844 * 2 ^ 59
def prefixEnd_2878844 : Nat := 4983230072969 + 3 ^ 40 * 2878844 * 2
def baseEnd_2878844 : Nat := 985487134208159828873629

theorem tailTrace_2878844 : CollatzResearch.WordTrace tailWord_2878844 prefixEnd_2878844 985487134208159828873629 := by
  unfold tailWord_2878844
  simp only [CollatzResearch.WordTrace]
  refine ⟨52500033391223665128333793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70000044521631553504445057 52500033391223665128333793)
  ·
    refine ⟨39375025043417748846250345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52500033391223665128333793 39375025043417748846250345)
    ·
      refine ⟨29531268782563311634687759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39375025043417748846250345 29531268782563311634687759)
      ·
        refine ⟨44296903173844967452031639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29531268782563311634687759 44296903173844967452031639)
        ·
          refine ⟨66445354760767451178047459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44296903173844967452031639 66445354760767451178047459)
          ·
            refine ⟨99668032141151176767071189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66445354760767451178047459 99668032141151176767071189)
            ·
              refine ⟨2335969503308230705478231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 99668032141151176767071189 2335969503308230705478231)
              ·
                refine ⟨3503954254962346058217347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2335969503308230705478231 3503954254962346058217347)
                ·
                  refine ⟨5255931382443519087326021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3503954254962346058217347 5255931382443519087326021)
                  ·
                    refine ⟨985487134208159828873629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5255931382443519087326021 985487134208159828873629)
                    ·
                      rfl

theorem cell22_2878844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 1, 1, 4].length) (baseStart_2878844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2878844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2878844 prefixEnd_2878844 := by exact prefixLift 2878844
  have htrace : WordTrace (prefixWord ++ tailWord_2878844) baseStart_2878844 baseEnd_2878844 := by
    simpa [prefixWord, tailWord_2878844, baseEnd_2878844] using wordTrace_append hprefix tailTrace_2878844
  have hstable : (prefixWord ++ tailWord_2878844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878844).length < 2 ^ (prefixWord ++ tailWord_2878844).sum := by decide
  have hdescent : baseEnd_2878844 < baseStart_2878844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878874 : List Nat := [3, 1, 1, 4, 1, 1, 1, 5, 2, 3]
def baseStart_2878874 : Nat := 118140960795 + 2878874 * 2 ^ 59
def prefixEnd_2878874 : Nat := 4983230072969 + 3 ^ 40 * 2878874 * 2
def baseEnd_2878874 : Nat := 985497403821249750623537

theorem tailTrace_2878874 : CollatzResearch.WordTrace tailWord_2878874 prefixEnd_2878874 985497403821249750623537 := by
  unfold tailWord_2878874
  simp only [CollatzResearch.WordTrace]
  refine ⟨26250290243084661345064919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70000773981559096920173117 26250290243084661345064919)
  ·
    refine ⟨39375435364626992017597379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26250290243084661345064919 39375435364626992017597379)
    ·
      refine ⟨59063153046940488026396069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39375435364626992017597379 59063153046940488026396069)
      ·
        refine ⟨11074341196301341504949263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59063153046940488026396069 11074341196301341504949263)
        ·
          refine ⟨16611511794452012257423895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11074341196301341504949263 16611511794452012257423895)
          ·
            refine ⟨24917267691678018386135843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16611511794452012257423895 24917267691678018386135843)
            ·
              refine ⟨37375901537517027579203765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24917267691678018386135843 37375901537517027579203765)
              ·
                refine ⟨3503990769142221335550353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37375901537517027579203765 3503990769142221335550353)
                ·
                  refine ⟨2627993076856666001662765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3503990769142221335550353 2627993076856666001662765)
                  ·
                    refine ⟨985497403821249750623537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2627993076856666001662765 985497403821249750623537)
                    ·
                      rfl

theorem cell22_2878874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 5, 2, 3].length) (baseStart_2878874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2878874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2878874 prefixEnd_2878874 := by exact prefixLift 2878874
  have htrace : WordTrace (prefixWord ++ tailWord_2878874) baseStart_2878874 baseEnd_2878874 := by
    simpa [prefixWord, tailWord_2878874, baseEnd_2878874] using wordTrace_append hprefix tailTrace_2878874
  have hstable : (prefixWord ++ tailWord_2878874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878874).length < 2 ^ (prefixWord ++ tailWord_2878874).sum := by decide
  have hdescent : baseEnd_2878874 < baseStart_2878874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878885 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 1, 9]
def baseStart_2878885 : Nat := 118140960795 + 2878885 * 2 ^ 59
def prefixEnd_2878885 : Nat := 4983230072969 + 3 ^ 40 * 2878885 * 2
def baseEnd_2878885 : Nat := 985501169346049388598503

theorem tailTrace_2878885 : CollatzResearch.WordTrace tailWord_2878885 prefixEnd_2878885 985501169346049388598503 := by
  unfold tailWord_2878885
  simp only [CollatzResearch.WordTrace]
  refine ⟨105001562175298794258910109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70001041450199196172606739 105001562175298794258910109)
  ·
    refine ⟨39375585815737047847091291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105001562175298794258910109 39375585815737047847091291)
    ·
      refine ⟨59063378723605571770636937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39375585815737047847091291 59063378723605571770636937)
      ·
        refine ⟨44297534042704178827977703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59063378723605571770636937 44297534042704178827977703)
        ·
          refine ⟨66446301064056268241966555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44297534042704178827977703 66446301064056268241966555)
          ·
            refine ⟨99669451596084402362949833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66446301064056268241966555 99669451596084402362949833)
            ·
              refine ⟨74752088697063301772212375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99669451596084402362949833 74752088697063301772212375)
              ·
                refine ⟨112128133045594952658318563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74752088697063301772212375 112128133045594952658318563)
                ·
                  refine ⟨168192199568392428987477845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112128133045594952658318563 168192199568392428987477845)
                  ·
                    refine ⟨985501169346049388598503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 168192199568392428987477845 985501169346049388598503)
                    ·
                      rfl

theorem cell22_2878885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_2878885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2878885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2878885 prefixEnd_2878885 := by exact prefixLift 2878885
  have htrace : WordTrace (prefixWord ++ tailWord_2878885) baseStart_2878885 baseEnd_2878885 := by
    simpa [prefixWord, tailWord_2878885, baseEnd_2878885] using wordTrace_append hprefix tailTrace_2878885
  have hstable : (prefixWord ++ tailWord_2878885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878885).length < 2 ^ (prefixWord ++ tailWord_2878885).sum := by decide
  have hdescent : baseEnd_2878885 < baseStart_2878885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878908 : List Nat := [2, 2, 2, 4, 2, 2, 1, 2, 2, 3]
def baseStart_2878908 : Nat := 118140960795 + 2878908 * 2 ^ 59
def prefixEnd_2878908 : Nat := 4983230072969 + 3 ^ 40 * 2878908 * 2
def baseEnd_2878908 : Nat := 985509042716084995273433

theorem tailTrace_2878908 : CollatzResearch.WordTrace tailWord_2878908 prefixEnd_2878908 985509042716084995273433 := by
  unfold tailWord_2878908
  simp only [CollatzResearch.WordTrace]
  refine ⟨52501200527107734593498689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70001600702810312791331585 52501200527107734593498689)
  ·
    refine ⟨39375900395330800945124017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52501200527107734593498689 39375900395330800945124017)
    ·
      refine ⟨29531925296498100708843013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39375900395330800945124017 29531925296498100708843013)
      ·
        refine ⟨5537235993093393882908065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29531925296498100708843013 5537235993093393882908065)
        ·
          refine ⟨4152926994820045412181049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5537235993093393882908065 4152926994820045412181049)
          ·
            refine ⟨3114695246115034059135787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4152926994820045412181049 3114695246115034059135787)
            ·
              refine ⟨4672042869172551088703681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3114695246115034059135787 4672042869172551088703681)
              ·
                refine ⟨3504032151879413316527761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4672042869172551088703681 3504032151879413316527761)
                ·
                  refine ⟨2628024113909559987395821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3504032151879413316527761 2628024113909559987395821)
                  ·
                    refine ⟨985509042716084995273433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2628024113909559987395821 985509042716084995273433)
                    ·
                      rfl

theorem cell22_2878908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 2, 2, 3].length) (baseStart_2878908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2878908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2878908 prefixEnd_2878908 := by exact prefixLift 2878908
  have htrace : WordTrace (prefixWord ++ tailWord_2878908) baseStart_2878908 baseEnd_2878908 := by
    simpa [prefixWord, tailWord_2878908, baseEnd_2878908] using wordTrace_append hprefix tailTrace_2878908
  have hstable : (prefixWord ++ tailWord_2878908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878908).length < 2 ^ (prefixWord ++ tailWord_2878908).sum := by decide
  have hdescent : baseEnd_2878908 < baseStart_2878908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2878919 : List Nat := [1, 1, 4, 1, 1, 3, 4, 1, 3, 3]
def baseStart_2878919 : Nat := 118140960795 + 2878919 * 2 ^ 59
def prefixEnd_2878919 : Nat := 4983230072969 + 3 ^ 40 * 2878919 * 2
def baseEnd_2878919 : Nat := 985512808240884633248399

theorem tailTrace_2878919 : CollatzResearch.WordTrace tailWord_2878919 prefixEnd_2878919 985512808240884633248399 := by
  unfold tailWord_2878919
  simp only [CollatzResearch.WordTrace]
  refine ⟨105002802257175618065647811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70001868171450412043765207 105002802257175618065647811)
  ·
    refine ⟨157504203385763427098471717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105002802257175618065647811 157504203385763427098471717)
    ·
      refine ⟨29532038134830642580963447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157504203385763427098471717 29532038134830642580963447)
      ·
        refine ⟨44298057202245963871445171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29532038134830642580963447 44298057202245963871445171)
        ·
          refine ⟨66447085803368945807167757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44298057202245963871445171 66447085803368945807167757)
          ·
            refine ⟨24917657176263354677687909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66447085803368945807167757 24917657176263354677687909)
            ·
              refine ⟨4672060720549379002066483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24917657176263354677687909 4672060720549379002066483)
              ·
                refine ⟨7008091080824068503099725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4672060720549379002066483 7008091080824068503099725)
                ·
                  refine ⟨2628034155309025688662397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7008091080824068503099725 2628034155309025688662397)
                  ·
                    refine ⟨985512808240884633248399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2628034155309025688662397 985512808240884633248399)
                    ·
                      rfl

theorem cell22_2878919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 3, 3].length) (baseStart_2878919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2878919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2878919 prefixEnd_2878919 := by exact prefixLift 2878919
  have htrace : WordTrace (prefixWord ++ tailWord_2878919) baseStart_2878919 baseEnd_2878919 := by
    simpa [prefixWord, tailWord_2878919, baseEnd_2878919] using wordTrace_append hprefix tailTrace_2878919
  have hstable : (prefixWord ++ tailWord_2878919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2878919).length < 2 ^ (prefixWord ++ tailWord_2878919).sum := by decide
  have hdescent : baseEnd_2878919 < baseStart_2878919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2878919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879007 : List Nat := [1, 1, 2, 4, 1, 1, 2, 3, 1, 6]
def baseStart_2879007 : Nat := 118140960795 + 2879007 * 2 ^ 59
def prefixEnd_2879007 : Nat := 4983230072969 + 3 ^ 40 * 2879007 * 2
def baseEnd_2879007 : Nat := 985542932439281737048129

theorem tailTrace_2879007 : CollatzResearch.WordTrace tailWord_2879007 prefixEnd_2879007 985542932439281737048129 := by
  unfold tailWord_2879007
  simp only [CollatzResearch.WordTrace]
  refine ⟨105006011880856809094851275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70004007920571206063234183 105006011880856809094851275)
  ·
    refine ⟨157509017821285213642276913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105006011880856809094851275 157509017821285213642276913)
    ·
      refine ⟨118131763365963910231707685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157509017821285213642276913 118131763365963910231707685)
      ·
        refine ⟨22149705631118233168445191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118131763365963910231707685 22149705631118233168445191)
        ·
          refine ⟨33224558446677349752667787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22149705631118233168445191 33224558446677349752667787)
          ·
            refine ⟨49836837670016024629001681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33224558446677349752667787 49836837670016024629001681)
            ·
              refine ⟨37377628252512018471751261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49836837670016024629001681 37377628252512018471751261)
              ·
                refine ⟨14016610594692006926906723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37377628252512018471751261 14016610594692006926906723)
                ·
                  refine ⟨21024915892038010390360085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14016610594692006926906723 21024915892038010390360085)
                  ·
                    refine ⟨985542932439281737048129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21024915892038010390360085 985542932439281737048129)
                    ·
                      rfl

theorem cell22_2879007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 6].length) (baseStart_2879007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2879007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2879007 prefixEnd_2879007 := by exact prefixLift 2879007
  have htrace : WordTrace (prefixWord ++ tailWord_2879007) baseStart_2879007 baseEnd_2879007 := by
    simpa [prefixWord, tailWord_2879007, baseEnd_2879007] using wordTrace_append hprefix tailTrace_2879007
  have hstable : (prefixWord ++ tailWord_2879007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879007).length < 2 ^ (prefixWord ++ tailWord_2879007).sum := by decide
  have hdescent : baseEnd_2879007 < baseStart_2879007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879009 : List Nat := [1, 2, 3, 2, 2, 3, 1, 2, 1, 5]
def baseStart_2879009 : Nat := 118140960795 + 2879009 * 2 ^ 59
def prefixEnd_2879009 : Nat := 4983230072969 + 3 ^ 40 * 2879009 * 2
def baseEnd_2879009 : Nat := 985543617080154398498123

theorem tailTrace_2879009 : CollatzResearch.WordTrace tailWord_2879009 prefixEnd_2879009 985543617080154398498123 := by
  unfold tailWord_2879009
  simp only [CollatzResearch.WordTrace]
  refine ⟨105006084826849563436424081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70004056551233042290949387 105006084826849563436424081)
  ·
    refine ⟨78754563620137172577318061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105006084826849563436424081 78754563620137172577318061)
    ·
      refine ⟨29532961357551439716494273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78754563620137172577318061 29532961357551439716494273)
      ·
        refine ⟨22149721018163579787370705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29532961357551439716494273 22149721018163579787370705)
        ·
          refine ⟨16612290763622684840528029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22149721018163579787370705 16612290763622684840528029)
          ·
            refine ⟨6229609036358506815198011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16612290763622684840528029 6229609036358506815198011)
            ·
              refine ⟨9344413554537760222797017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6229609036358506815198011 9344413554537760222797017)
              ·
                refine ⟨7008310165903320167097763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9344413554537760222797017 7008310165903320167097763)
                ·
                  refine ⟨10512465248854980250646645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7008310165903320167097763 10512465248854980250646645)
                  ·
                    refine ⟨985543617080154398498123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10512465248854980250646645 985543617080154398498123)
                    ·
                      rfl

theorem cell22_2879009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_2879009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2879009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2879009 prefixEnd_2879009 := by exact prefixLift 2879009
  have htrace : WordTrace (prefixWord ++ tailWord_2879009) baseStart_2879009 baseEnd_2879009 := by
    simpa [prefixWord, tailWord_2879009, baseEnd_2879009] using wordTrace_append hprefix tailTrace_2879009
  have hstable : (prefixWord ++ tailWord_2879009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879009).length < 2 ^ (prefixWord ++ tailWord_2879009).sum := by decide
  have hdescent : baseEnd_2879009 < baseStart_2879009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879039 : List Nat := [1, 1, 2, 2, 3, 5, 1, 7]
def baseStart_2879039 : Nat := 118140960795 + 2879039 * 2 ^ 59
def prefixEnd_2879039 : Nat := 4983230072969 + 3 ^ 40 * 2879039 * 2
def baseEnd_2879039 : Nat := 109505987410360480027559

theorem tailTrace_2879039 : CollatzResearch.WordTrace tailWord_2879039 prefixEnd_2879039 109505987410360480027559 := by
  unfold tailWord_2879039
  simp only [CollatzResearch.WordTrace]
  refine ⟨105007179016740878560016171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70004786011160585706677447 105007179016740878560016171)
  ·
    refine ⟨157510768525111317840024257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105007179016740878560016171 157510768525111317840024257)
    ·
      refine ⟨118133076393833488380018193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157510768525111317840024257 118133076393833488380018193)
      ·
        refine ⟨88599807295375116285013645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118133076393833488380018193 88599807295375116285013645)
        ·
          refine ⟨33224927735765668606880117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88599807295375116285013645 33224927735765668606880117)
          ·
            refine ⟨3114836975228031431895011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33224927735765668606880117 3114836975228031431895011)
            ·
              refine ⟨4672255462842047147842517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3114836975228031431895011 4672255462842047147842517)
              ·
                refine ⟨109505987410360480027559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4672255462842047147842517 109505987410360480027559)
                ·
                  rfl

theorem cell22_2879039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 7].length) (baseStart_2879039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2879039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2879039 prefixEnd_2879039 := by exact prefixLift 2879039
  have htrace : WordTrace (prefixWord ++ tailWord_2879039) baseStart_2879039 baseEnd_2879039 := by
    simpa [prefixWord, tailWord_2879039, baseEnd_2879039] using wordTrace_append hprefix tailTrace_2879039
  have hstable : (prefixWord ++ tailWord_2879039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879039).length < 2 ^ (prefixWord ++ tailWord_2879039).sum := by decide
  have hdescent : baseEnd_2879039 < baseStart_2879039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879062 : List Nat := [5, 2, 2, 2, 1, 1, 2, 3, 4]
def baseStart_2879062 : Nat := 118140960795 + 2879062 * 2 ^ 59
def prefixEnd_2879062 : Nat := 4983230072969 + 3 ^ 40 * 2879062 * 2
def baseEnd_2879062 : Nat := 328520586687759975640987

theorem tailTrace_2879062 : CollatzResearch.WordTrace tailWord_2879062 prefixEnd_2879062 328520586687759975640987 := by
  unfold tailWord_2879062
  simp only [CollatzResearch.WordTrace]
  refine ⟨6563001118478597093006465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70005345263771702325402293 6563001118478597093006465)
  ·
    refine ⟨4922250838858947819754849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6563001118478597093006465 4922250838858947819754849)
    ·
      refine ⟨3691688129144210864816137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4922250838858947819754849 3691688129144210864816137)
      ·
        refine ⟨2768766096858158148612103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3691688129144210864816137 2768766096858158148612103)
        ·
          refine ⟨4153149145287237222918155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2768766096858158148612103 4153149145287237222918155)
          ·
            refine ⟨6229723717930855834377233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4153149145287237222918155 6229723717930855834377233)
            ·
              refine ⟨4672292788448141875782925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6229723717930855834377233 4672292788448141875782925)
              ·
                refine ⟨1752109795668053203418597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4672292788448141875782925 1752109795668053203418597)
                ·
                  refine ⟨328520586687759975640987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1752109795668053203418597 328520586687759975640987)
                  ·
                    rfl

theorem cell22_2879062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_2879062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2879062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2879062 prefixEnd_2879062 := by exact prefixLift 2879062
  have htrace : WordTrace (prefixWord ++ tailWord_2879062) baseStart_2879062 baseEnd_2879062 := by
    simpa [prefixWord, tailWord_2879062, baseEnd_2879062] using wordTrace_append hprefix tailTrace_2879062
  have hstable : (prefixWord ++ tailWord_2879062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879062).length < 2 ^ (prefixWord ++ tailWord_2879062).sum := by decide
  have hdescent : baseEnd_2879062 < baseStart_2879062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879088 : List Nat := [2, 1, 1, 1, 6, 1, 2, 4, 1, 3]
def baseStart_2879088 : Nat := 118140960795 + 2879088 * 2 ^ 59
def prefixEnd_2879088 : Nat := 4983230072969 + 3 ^ 40 * 2879088 * 2
def baseEnd_2879088 : Nat := 985570660394624525772881

theorem tailTrace_2879088 : CollatzResearch.WordTrace tailWord_2879088 prefixEnd_2879088 985570660394624525772881 := by
  unfold tailWord_2879088
  simp only [CollatzResearch.WordTrace]
  refine ⟨52504483096781679964274959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70005977462375573285699945 52504483096781679964274959)
  ·
    refine ⟨78756724645172519946412439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52504483096781679964274959 78756724645172519946412439)
    ·
      refine ⟨118135086967758779919618659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78756724645172519946412439 118135086967758779919618659)
      ·
        refine ⟨177202630451638169879427989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118135086967758779919618659 177202630451638169879427989)
        ·
          refine ⟨8306373302420539213098187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 177202630451638169879427989 8306373302420539213098187)
          ·
            refine ⟨12459559953630808819647281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8306373302420539213098187 12459559953630808819647281)
            ·
              refine ⟨9344669965223106614735461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12459559953630808819647281 9344669965223106614735461)
              ·
                refine ⟨1752125618479332490262899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9344669965223106614735461 1752125618479332490262899)
                ·
                  refine ⟨2628188427718998735394349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1752125618479332490262899 2628188427718998735394349)
                  ·
                    refine ⟨985570660394624525772881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2628188427718998735394349 985570660394624525772881)
                    ·
                      rfl

theorem cell22_2879088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 4, 1, 3].length) (baseStart_2879088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2879088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2879088 prefixEnd_2879088 := by exact prefixLift 2879088
  have htrace : WordTrace (prefixWord ++ tailWord_2879088) baseStart_2879088 baseEnd_2879088 := by
    simpa [prefixWord, tailWord_2879088, baseEnd_2879088] using wordTrace_append hprefix tailTrace_2879088
  have hstable : (prefixWord ++ tailWord_2879088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879088).length < 2 ^ (prefixWord ++ tailWord_2879088).sum := by decide
  have hdescent : baseEnd_2879088 < baseStart_2879088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879122 : List Nat := [3, 2, 3, 1, 3, 2, 1, 3, 1, 3]
def baseStart_2879122 : Nat := 118140960795 + 2879122 * 2 ^ 59
def prefixEnd_2879122 : Nat := 4983230072969 + 3 ^ 40 * 2879122 * 2
def baseEnd_2879122 : Nat := 985582299289459770422777

theorem tailTrace_2879122 : CollatzResearch.WordTrace tailWord_2879122 prefixEnd_2879122 985582299289459770422777 := by
  unfold tailWord_2879122
  simp only [CollatzResearch.WordTrace]
  refine ⟨26252551568860045933821905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70006804183626789156858413 26252551568860045933821905)
  ·
    refine ⟨19689413676645034450366429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26252551568860045933821905 19689413676645034450366429)
    ·
      refine ⟨7383530128741887918887411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19689413676645034450366429 7383530128741887918887411)
      ·
        refine ⟨11075295193112831878331117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7383530128741887918887411 11075295193112831878331117)
        ·
          refine ⟨4153235697417311954374169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11075295193112831878331117 4153235697417311954374169)
          ·
            refine ⟨3114926773062983965780627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4153235697417311954374169 3114926773062983965780627)
            ·
              refine ⟨4672390159594475948670941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3114926773062983965780627 4672390159594475948670941)
              ·
                refine ⟨1752146309847928480751603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4672390159594475948670941 1752146309847928480751603)
                ·
                  refine ⟨2628219464771892721127405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1752146309847928480751603 2628219464771892721127405)
                  ·
                    refine ⟨985582299289459770422777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2628219464771892721127405 985582299289459770422777)
                    ·
                      rfl

theorem cell22_2879122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_2879122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2879122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2879122 prefixEnd_2879122 := by exact prefixLift 2879122
  have htrace : WordTrace (prefixWord ++ tailWord_2879122) baseStart_2879122 baseEnd_2879122 := by
    simpa [prefixWord, tailWord_2879122, baseEnd_2879122] using wordTrace_append hprefix tailTrace_2879122
  have hstable : (prefixWord ++ tailWord_2879122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879122).length < 2 ^ (prefixWord ++ tailWord_2879122).sum := by decide
  have hdescent : baseEnd_2879122 < baseStart_2879122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879176 : List Nat := [2, 1, 3, 1, 2, 2, 4, 1, 2, 4]
def baseStart_2879176 : Nat := 118140960795 + 2879176 * 2 ^ 59
def prefixEnd_2879176 : Nat := 4983230072969 + 3 ^ 40 * 2879176 * 2
def baseEnd_2879176 : Nat := 985600784593021629572611

theorem tailTrace_2879176 : CollatzResearch.WordTrace tailWord_2879176 prefixEnd_2879176 985600784593021629572611 := by
  unfold tailWord_2879176
  simp only [CollatzResearch.WordTrace]
  refine ⟨52506087908622275478876691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70008117211496367305168921 52506087908622275478876691)
  ·
    refine ⟨78759131862933413218315037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52506087908622275478876691 78759131862933413218315037)
    ·
      refine ⟨29534674448600029956868139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78759131862933413218315037 29534674448600029956868139)
      ·
        refine ⟨44302011672900044935302209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29534674448600029956868139 44302011672900044935302209)
        ·
          refine ⟨33226508754675033701476657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44302011672900044935302209 33226508754675033701476657)
          ·
            refine ⟨24919881566006275276107493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33226508754675033701476657 24919881566006275276107493)
            ·
              refine ⟨4672477793626176614270155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24919881566006275276107493 4672477793626176614270155)
              ·
                refine ⟨7008716690439264921405233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4672477793626176614270155 7008716690439264921405233)
                ·
                  refine ⟨5256537517829448691053925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7008716690439264921405233 5256537517829448691053925)
                  ·
                    refine ⟨985600784593021629572611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5256537517829448691053925 985600784593021629572611)
                    ·
                      rfl

theorem cell22_2879176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_2879176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2879176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2879176 prefixEnd_2879176 := by exact prefixLift 2879176
  have htrace : WordTrace (prefixWord ++ tailWord_2879176) baseStart_2879176 baseEnd_2879176 := by
    simpa [prefixWord, tailWord_2879176, baseEnd_2879176] using wordTrace_append hprefix tailTrace_2879176
  have hstable : (prefixWord ++ tailWord_2879176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879176).length < 2 ^ (prefixWord ++ tailWord_2879176).sum := by decide
  have hdescent : baseEnd_2879176 < baseStart_2879176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879204 : List Nat := [2, 3, 1, 1, 1, 3, 1, 1, 1, 8]
def baseStart_2879204 : Nat := 118140960795 + 2879204 * 2 ^ 59
def prefixEnd_2879204 : Nat := 4983230072969 + 3 ^ 40 * 2879204 * 2
def baseEnd_2879204 : Nat := 985610369565238889872525

theorem tailTrace_2879204 : CollatzResearch.WordTrace tailWord_2879204 prefixEnd_2879204 985610369565238889872525 := by
  unfold tailWord_2879204
  simp only [CollatzResearch.WordTrace]
  refine ⟨52506598530571555869886333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70008798040762074493181777 52506598530571555869886333)
  ·
    refine ⟨19689974448964333451207375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52506598530571555869886333 19689974448964333451207375)
    ·
      refine ⟨29534961673446500176811063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19689974448964333451207375 29534961673446500176811063)
      ·
        refine ⟨44302442510169750265216595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29534961673446500176811063 44302442510169750265216595)
        ·
          refine ⟨66453663765254625397824893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44302442510169750265216595 66453663765254625397824893)
          ·
            refine ⟨24920123911970484524184335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66453663765254625397824893 24920123911970484524184335)
            ·
              refine ⟨37380185867955726786276503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24920123911970484524184335 37380185867955726786276503)
              ·
                refine ⟨56070278801933590179414755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37380185867955726786276503 56070278801933590179414755)
                ·
                  refine ⟨84105418202900385269122133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56070278801933590179414755 84105418202900385269122133)
                  ·
                    refine ⟨985610369565238889872525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 84105418202900385269122133 985610369565238889872525)
                    ·
                      rfl

theorem cell22_2879204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_2879204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2879204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2879204 prefixEnd_2879204 := by exact prefixLift 2879204
  have htrace : WordTrace (prefixWord ++ tailWord_2879204) baseStart_2879204 baseEnd_2879204 := by
    simpa [prefixWord, tailWord_2879204, baseEnd_2879204] using wordTrace_append hprefix tailTrace_2879204
  have hstable : (prefixWord ++ tailWord_2879204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879204).length < 2 ^ (prefixWord ++ tailWord_2879204).sum := by decide
  have hdescent : baseEnd_2879204 < baseStart_2879204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879240 : List Nat := [2, 1, 3, 2, 2, 1, 4, 3, 1, 3]
def baseStart_2879240 : Nat := 118140960795 + 2879240 * 2 ^ 59
def prefixEnd_2879240 : Nat := 4983230072969 + 3 ^ 40 * 2879240 * 2
def baseEnd_2879240 : Nat := 985622693100946795972415

theorem tailTrace_2879240 : CollatzResearch.WordTrace tailWord_2879240 prefixEnd_2879240 985622693100946795972415 := by
  unfold tailWord_2879240
  simp only [CollatzResearch.WordTrace]
  refine ⟨52507255044506344944041587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70009673392675126592055449 52507255044506344944041587)
  ·
    refine ⟨78760882566759517416062381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52507255044506344944041587 78760882566759517416062381)
    ·
      refine ⟨29535330962534819031023393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78760882566759517416062381 29535330962534819031023393)
      ·
        refine ⟨22151498221901114273267545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29535330962534819031023393 22151498221901114273267545)
        ·
          refine ⟨16613623666425835704950659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22151498221901114273267545 16613623666425835704950659)
          ·
            refine ⟨24920435499638753557425989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16613623666425835704950659 24920435499638753557425989)
            ·
              refine ⟨4672581656182266292017373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24920435499638753557425989 4672581656182266292017373)
              ·
                refine ⟨1752218121068349859506515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4672581656182266292017373 1752218121068349859506515)
                ·
                  refine ⟨2628327181602524789259773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1752218121068349859506515 2628327181602524789259773)
                  ·
                    refine ⟨985622693100946795972415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2628327181602524789259773 985622693100946795972415)
                    ·
                      rfl

theorem cell22_2879240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 3, 1, 3].length) (baseStart_2879240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2879240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2879240 prefixEnd_2879240 := by exact prefixLift 2879240
  have htrace : WordTrace (prefixWord ++ tailWord_2879240) baseStart_2879240 baseEnd_2879240 := by
    simpa [prefixWord, tailWord_2879240, baseEnd_2879240] using wordTrace_append hprefix tailTrace_2879240
  have hstable : (prefixWord ++ tailWord_2879240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879240).length < 2 ^ (prefixWord ++ tailWord_2879240).sum := by decide
  have hdescent : baseEnd_2879240 < baseStart_2879240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879253 : List Nat := [1, 3, 2, 1, 2, 5, 1, 2, 5]
def baseStart_2879253 : Nat := 118140960795 + 2879253 * 2 ^ 59
def prefixEnd_2879253 : Nat := 4983230072969 + 3 ^ 40 * 2879253 * 2
def baseEnd_2879253 : Nat := 328542381088873031799125

theorem tailTrace_2879253 : CollatzResearch.WordTrace tailWord_2879253 prefixEnd_2879253 328542381088873031799125 := by
  unfold tailWord_2879253
  simp only [CollatzResearch.WordTrace]
  refine ⟨105014984237965593108306413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70009989491977062072204275 105014984237965593108306413)
  ·
    refine ⟨39380619089237097415614905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105014984237965593108306413 39380619089237097415614905)
    ·
      refine ⟨29535464316927823061711179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39380619089237097415614905 29535464316927823061711179)
      ·
        refine ⟨44303196475391734592566769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29535464316927823061711179 44303196475391734592566769)
        ·
          refine ⟨33227397356543800944425077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44303196475391734592566769 33227397356543800944425077)
          ·
            refine ⟨3115068502175981338539851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33227397356543800944425077 3115068502175981338539851)
            ·
              refine ⟨4672602753263972007809777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3115068502175981338539851 4672602753263972007809777)
              ·
                refine ⟨3504452064947979005857333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4672602753263972007809777 3504452064947979005857333)
                ·
                  refine ⟨328542381088873031799125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3504452064947979005857333 328542381088873031799125)
                  ·
                    rfl

theorem cell22_2879253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 2, 5].length) (baseStart_2879253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2879253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2879253 prefixEnd_2879253 := by exact prefixLift 2879253
  have htrace : WordTrace (prefixWord ++ tailWord_2879253) baseStart_2879253 baseEnd_2879253 := by
    simpa [prefixWord, tailWord_2879253, baseEnd_2879253] using wordTrace_append hprefix tailTrace_2879253
  have hstable : (prefixWord ++ tailWord_2879253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879253).length < 2 ^ (prefixWord ++ tailWord_2879253).sum := by decide
  have hdescent : baseEnd_2879253 < baseStart_2879253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879281 : List Nat := [1, 2, 2, 3, 2, 2, 2, 2, 6]
def baseStart_2879281 : Nat := 118140960795 + 2879281 * 2 ^ 59
def prefixEnd_2879281 : Nat := 4983230072969 + 3 ^ 40 * 2879281 * 2
def baseEnd_2879281 : Nat := 328545576079612118565763

theorem tailTrace_2879281 : CollatzResearch.WordTrace tailWord_2879281 prefixEnd_2879281 328545576079612118565763 := by
  unfold tailWord_2879281
  simp only [CollatzResearch.WordTrace]
  refine ⟨105016005481864153890325697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70010670321242769260217131 105016005481864153890325697)
  ·
    refine ⟨78762004111398115417744273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105016005481864153890325697 78762004111398115417744273)
    ·
      refine ⟨59071503083548586563308205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78762004111398115417744273 59071503083548586563308205)
      ·
        refine ⟨22151813656330719961240577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59071503083548586563308205 22151813656330719961240577)
        ·
          refine ⟨16613860242248039970930433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22151813656330719961240577 16613860242248039970930433)
          ·
            refine ⟨12460395181686029978197825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16613860242248039970930433 12460395181686029978197825)
            ·
              refine ⟨9345296386264522483648369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12460395181686029978197825 9345296386264522483648369)
              ·
                refine ⟨7008972289698391862736277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9345296386264522483648369 7008972289698391862736277)
                ·
                  refine ⟨328545576079612118565763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7008972289698391862736277 328545576079612118565763)
                  ·
                    rfl

theorem cell22_2879281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 6].length) (baseStart_2879281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2879281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2879281 prefixEnd_2879281 := by exact prefixLift 2879281
  have htrace : WordTrace (prefixWord ++ tailWord_2879281) baseStart_2879281 baseEnd_2879281 := by
    simpa [prefixWord, tailWord_2879281, baseEnd_2879281] using wordTrace_append hprefix tailTrace_2879281
  have hstable : (prefixWord ++ tailWord_2879281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879281).length < 2 ^ (prefixWord ++ tailWord_2879281).sum := by decide
  have hdescent : baseEnd_2879281 < baseStart_2879281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879313 : List Nat := [1, 2, 2, 1, 5, 1, 2, 1, 4, 3]
def baseStart_2879313 : Nat := 118140960795 + 2879313 * 2 ^ 59
def prefixEnd_2879313 : Nat := 4983230072969 + 3 ^ 40 * 2879313 * 2
def baseEnd_2879313 : Nat := 985647682492798938897191

theorem tailTrace_2879313 : CollatzResearch.WordTrace tailWord_2879313 prefixEnd_2879313 985647682492798938897191 := by
  unfold tailWord_2879313
  simp only [CollatzResearch.WordTrace]
  refine ⟨105017172617748223355490593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70011448411832148903660395 105017172617748223355490593)
  ·
    refine ⟨78762879463311167516617945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105017172617748223355490593 78762879463311167516617945)
    ·
      refine ⟨59072159597483375637463459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78762879463311167516617945 59072159597483375637463459)
      ·
        refine ⟨88608239396225063456195189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59072159597483375637463459 88608239396225063456195189)
        ·
          refine ⟨8307022443396099699018299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88608239396225063456195189 8307022443396099699018299)
          ·
            refine ⟨12460533665094149548527449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8307022443396099699018299 12460533665094149548527449)
            ·
              refine ⟨9345400248820612161395587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12460533665094149548527449 9345400248820612161395587)
              ·
                refine ⟨14018100373230918242093381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9345400248820612161395587 14018100373230918242093381)
                ·
                  refine ⟨2628393819980797170392509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14018100373230918242093381 2628393819980797170392509)
                  ·
                    refine ⟨985647682492798938897191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2628393819980797170392509 985647682492798938897191)
                    ·
                      rfl

theorem cell22_2879313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 4, 3].length) (baseStart_2879313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2879313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2879313 prefixEnd_2879313 := by exact prefixLift 2879313
  have htrace : WordTrace (prefixWord ++ tailWord_2879313) baseStart_2879313 baseEnd_2879313 := by
    simpa [prefixWord, tailWord_2879313, baseEnd_2879313] using wordTrace_append hprefix tailTrace_2879313
  have hstable : (prefixWord ++ tailWord_2879313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879313).length < 2 ^ (prefixWord ++ tailWord_2879313).sum := by decide
  have hdescent : baseEnd_2879313 < baseStart_2879313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879341 : List Nat := [1, 5, 1, 1, 1, 1, 2, 1, 2, 7]
def baseStart_2879341 : Nat := 118140960795 + 2879341 * 2 ^ 59
def prefixEnd_2879341 : Nat := 4983230072969 + 3 ^ 40 * 2879341 * 2
def baseEnd_2879341 : Nat := 985657267465016199197105

theorem tailTrace_2879341 : CollatzResearch.WordTrace tailWord_2879341 prefixEnd_2879341 985657267465016199197105 := by
  unfold tailWord_2879341
  simp only [CollatzResearch.WordTrace]
  refine ⟨105018193861646784137509877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70012129241097856091673251 105018193861646784137509877)
  ·
    refine ⟨9845455674529386012891551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105018193861646784137509877 9845455674529386012891551)
    ·
      refine ⟨14768183511794079019337327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9845455674529386012891551 14768183511794079019337327)
      ·
        refine ⟨22152275267691118529005991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14768183511794079019337327 22152275267691118529005991)
        ·
          refine ⟨33228412901536677793508987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22152275267691118529005991 33228412901536677793508987)
          ·
            refine ⟨49842619352305016690263481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33228412901536677793508987 49842619352305016690263481)
            ·
              refine ⟨37381964514228762517697611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49842619352305016690263481 37381964514228762517697611)
              ·
                refine ⟨56072946771343143776546417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37381964514228762517697611 56072946771343143776546417)
                ·
                  refine ⟨42054710078507357832409813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56072946771343143776546417 42054710078507357832409813)
                  ·
                    refine ⟨985657267465016199197105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42054710078507357832409813 985657267465016199197105)
                    ·
                      rfl

theorem cell22_2879341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_2879341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2879341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2879341 prefixEnd_2879341 := by exact prefixLift 2879341
  have htrace : WordTrace (prefixWord ++ tailWord_2879341) baseStart_2879341 baseEnd_2879341 := by
    simpa [prefixWord, tailWord_2879341, baseEnd_2879341] using wordTrace_append hprefix tailTrace_2879341
  have hstable : (prefixWord ++ tailWord_2879341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879341).length < 2 ^ (prefixWord ++ tailWord_2879341).sum := by decide
  have hdescent : baseEnd_2879341 < baseStart_2879341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879416 : List Nat := [2, 1, 2, 1, 2, 3, 1, 2, 8]
def baseStart_2879416 : Nat := 118140960795 + 2879416 * 2 ^ 59
def prefixEnd_2879416 : Nat := 4983230072969 + 3 ^ 40 * 2879416 * 2
def baseEnd_2879416 : Nat := 328560980499247001190625

theorem tailTrace_2879416 : CollatzResearch.WordTrace tailWord_2879416 prefixEnd_2879416 328560980499247001190625 := by
  unfold tailWord_2879416
  simp only [CollatzResearch.WordTrace]
  refine ⟨52510464668187535973245051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70013952890916714630993401 52510464668187535973245051)
  ·
    refine ⟨78765697002281303959867577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52510464668187535973245051 78765697002281303959867577)
    ·
      refine ⟨59074272751710977969900683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78765697002281303959867577 59074272751710977969900683)
      ·
        refine ⟨88611409127566466954851025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59074272751710977969900683 88611409127566466954851025)
        ·
          refine ⟨66458556845674850216138269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88611409127566466954851025 66458556845674850216138269)
          ·
            refine ⟨24921958817128068831051851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66458556845674850216138269 24921958817128068831051851)
            ·
              refine ⟨37382938225692103246577777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24921958817128068831051851 37382938225692103246577777)
              ·
                refine ⟨28037203669269077434933333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37382938225692103246577777 28037203669269077434933333)
                ·
                  refine ⟨328560980499247001190625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28037203669269077434933333 328560980499247001190625)
                  ·
                    rfl

theorem cell22_2879416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 8].length) (baseStart_2879416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2879416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2879416 prefixEnd_2879416 := by exact prefixLift 2879416
  have htrace : WordTrace (prefixWord ++ tailWord_2879416) baseStart_2879416 baseEnd_2879416 := by
    simpa [prefixWord, tailWord_2879416, baseEnd_2879416] using wordTrace_append hprefix tailTrace_2879416
  have hstable : (prefixWord ++ tailWord_2879416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879416).length < 2 ^ (prefixWord ++ tailWord_2879416).sum := by decide
  have hdescent : baseEnd_2879416 < baseStart_2879416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879544 : List Nat := [2, 1, 2, 1, 6, 1, 1, 4, 1, 3]
def baseStart_2879544 : Nat := 118140960795 + 2879544 * 2 ^ 59
def prefixEnd_2879544 : Nat := 4983230072969 + 3 ^ 40 * 2879544 * 2
def baseEnd_2879544 : Nat := 985726758513591336371483

theorem tailTrace_2879544 : CollatzResearch.WordTrace tailWord_2879544 prefixEnd_2879544 985726758513591336371483 := by
  unfold tailWord_2879544
  simp only [CollatzResearch.WordTrace]
  refine ⟨52512798939955674903574843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70017065253274233204766457 52512798939955674903574843)
  ·
    refine ⟨78769198409933512355362265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52512798939955674903574843 78769198409933512355362265)
    ·
      refine ⟨59076898807450134266521699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78769198409933512355362265 59076898807450134266521699)
      ·
        refine ⟨88615348211175201399782549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59076898807450134266521699 88615348211175201399782549)
        ·
          refine ⟨4153844447398837565614807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 88615348211175201399782549 4153844447398837565614807)
          ·
            refine ⟨6230766671098256348422211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4153844447398837565614807 6230766671098256348422211)
            ·
              refine ⟨9346150006647384522633317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6230766671098256348422211 9346150006647384522633317)
              ·
                refine ⟨1752403126246384597993747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9346150006647384522633317 1752403126246384597993747)
                ·
                  refine ⟨2628604689369576896990621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1752403126246384597993747 2628604689369576896990621)
                  ·
                    refine ⟨985726758513591336371483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2628604689369576896990621 985726758513591336371483)
                    ·
                      rfl

theorem cell22_2879544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 4, 1, 3].length) (baseStart_2879544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2879544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2879544 prefixEnd_2879544 := by exact prefixLift 2879544
  have htrace : WordTrace (prefixWord ++ tailWord_2879544) baseStart_2879544 baseEnd_2879544 := by
    simpa [prefixWord, tailWord_2879544, baseEnd_2879544] using wordTrace_append hprefix tailTrace_2879544
  have hstable : (prefixWord ++ tailWord_2879544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879544).length < 2 ^ (prefixWord ++ tailWord_2879544).sum := by decide
  have hdescent : baseEnd_2879544 < baseStart_2879544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879583 : List Nat := [1, 1, 2, 3, 1, 1, 2, 3, 3, 5]
def baseStart_2879583 : Nat := 118140960795 + 2879583 * 2 ^ 59
def prefixEnd_2879583 : Nat := 4983230072969 + 3 ^ 40 * 2879583 * 2
def baseEnd_2879583 : Nat := 985740109010608234646363

theorem tailTrace_2879583 : CollatzResearch.WordTrace tailWord_2879583 prefixEnd_2879583 985740109010608234646363 := by
  unfold tailWord_2879583
  simp only [CollatzResearch.WordTrace]
  refine ⟨105027020326770059467819403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70018013551180039645212935 105027020326770059467819403)
  ·
    refine ⟨157540530490155089201729105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105027020326770059467819403 157540530490155089201729105)
    ·
      refine ⟨118155397867616316901296829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157540530490155089201729105 118155397867616316901296829)
      ·
        refine ⟨44308274200356118837986311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118155397867616316901296829 44308274200356118837986311)
        ·
          refine ⟨66462411300534178256979467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44308274200356118837986311 66462411300534178256979467)
          ·
            refine ⟨99693616950801267385469201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66462411300534178256979467 99693616950801267385469201)
            ·
              refine ⟨74770212713100950539101901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99693616950801267385469201 74770212713100950539101901)
              ·
                refine ⟨28038829767412856452163213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74770212713100950539101901 28038829767412856452163213)
                ·
                  refine ⟨10514561162779821169561205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28038829767412856452163213 10514561162779821169561205)
                  ·
                    refine ⟨985740109010608234646363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10514561162779821169561205 985740109010608234646363)
                    ·
                      rfl

theorem cell22_2879583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 5].length) (baseStart_2879583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2879583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2879583 prefixEnd_2879583 := by exact prefixLift 2879583
  have htrace : WordTrace (prefixWord ++ tailWord_2879583) baseStart_2879583 baseEnd_2879583 := by
    simpa [prefixWord, tailWord_2879583, baseEnd_2879583] using wordTrace_append hprefix tailTrace_2879583
  have hstable : (prefixWord ++ tailWord_2879583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879583).length < 2 ^ (prefixWord ++ tailWord_2879583).sum := by decide
  have hdescent : baseEnd_2879583 < baseStart_2879583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879587 : List Nat := [1, 1, 1, 5, 1, 1, 6, 1, 1, 4]
def baseStart_2879587 : Nat := 118140960795 + 2879587 * 2 ^ 59
def prefixEnd_2879587 : Nat := 4983230072969 + 3 ^ 40 * 2879587 * 2
def baseEnd_2879587 : Nat := 985741478292353557546351

theorem tailTrace_2879587 : CollatzResearch.WordTrace tailWord_2879587 prefixEnd_2879587 985741478292353557546351 := by
  unfold tailWord_2879587
  simp only [CollatzResearch.WordTrace]
  refine ⟨105027166218755568150965015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70018110812503712100643343 105027166218755568150965015)
  ·
    refine ⟨157540749328133352226447523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105027166218755568150965015 157540749328133352226447523)
    ·
      refine ⟨236311123992200028339671285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157540749328133352226447523 236311123992200028339671285)
      ·
        refine ⟨22154167874268752656844183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 236311123992200028339671285 22154167874268752656844183)
        ·
          refine ⟨33231251811403128985266275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22154167874268752656844183 33231251811403128985266275)
          ·
            refine ⟨49846877717104693477899413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33231251811403128985266275 49846877717104693477899413)
            ·
              refine ⟨2336572392989282506776535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 49846877717104693477899413 2336572392989282506776535)
              ·
                refine ⟨3504858589483923760164803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2336572392989282506776535 3504858589483923760164803)
                ·
                  refine ⟨5257287884225885640247205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3504858589483923760164803 5257287884225885640247205)
                  ·
                    refine ⟨985741478292353557546351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5257287884225885640247205 985741478292353557546351)
                    ·
                      rfl

theorem cell22_2879587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 1, 1, 4].length) (baseStart_2879587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2879587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2879587 prefixEnd_2879587 := by exact prefixLift 2879587
  have htrace : WordTrace (prefixWord ++ tailWord_2879587) baseStart_2879587 baseEnd_2879587 := by
    simpa [prefixWord, tailWord_2879587, baseEnd_2879587] using wordTrace_append hprefix tailTrace_2879587
  have hstable : (prefixWord ++ tailWord_2879587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879587).length < 2 ^ (prefixWord ++ tailWord_2879587).sum := by decide
  have hdescent : baseEnd_2879587 < baseStart_2879587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879602 : List Nat := [3, 2, 1, 2, 2, 2, 2, 4, 4]
def baseStart_2879602 : Nat := 118140960795 + 2879602 * 2 ^ 59
def prefixEnd_2879602 : Nat := 4983230072969 + 3 ^ 40 * 2879602 * 2
def baseEnd_2879602 : Nat := 328582204366299506140435

theorem tailTrace_2879602 : CollatzResearch.WordTrace tailWord_2879602 prefixEnd_2879602 328582204366299506140435 := by
  unfold tailWord_2879602
  simp only [CollatzResearch.WordTrace]
  refine ⟨26256928328425306428190265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70018475542467483808507373 26256928328425306428190265)
  ·
    refine ⟨19692696246318979821142699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26256928328425306428190265 19692696246318979821142699)
    ·
      refine ⟨29539044369478469731714049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19692696246318979821142699 29539044369478469731714049)
      ·
        refine ⟨22154283277108852298785537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29539044369478469731714049 22154283277108852298785537)
        ·
          refine ⟨16615712457831639224089153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22154283277108852298785537 16615712457831639224089153)
          ·
            refine ⟨12461784343373729418066865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16615712457831639224089153 12461784343373729418066865)
            ·
              refine ⟨9346338257530297063550149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12461784343373729418066865 9346338257530297063550149)
              ·
                refine ⟨1752438423286930699415653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9346338257530297063550149 1752438423286930699415653)
                ·
                  refine ⟨328582204366299506140435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1752438423286930699415653 328582204366299506140435)
                  ·
                    rfl

theorem cell22_2879602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 4, 4].length) (baseStart_2879602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2879602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2879602 prefixEnd_2879602 := by exact prefixLift 2879602
  have htrace : WordTrace (prefixWord ++ tailWord_2879602) baseStart_2879602 baseEnd_2879602 := by
    simpa [prefixWord, tailWord_2879602, baseEnd_2879602] using wordTrace_append hprefix tailTrace_2879602
  have hstable : (prefixWord ++ tailWord_2879602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879602).length < 2 ^ (prefixWord ++ tailWord_2879602).sum := by decide
  have hdescent : baseEnd_2879602 < baseStart_2879602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879643 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 4, 6]
def baseStart_2879643 : Nat := 118140960795 + 2879643 * 2 ^ 59
def prefixEnd_2879643 : Nat := 4983230072969 + 3 ^ 40 * 2879643 * 2
def baseEnd_2879643 : Nat := 985760648236788078146179

theorem tailTrace_2879643 : CollatzResearch.WordTrace tailWord_2879643 prefixEnd_2879643 985760648236788078146179 := by
  unfold tailWord_2879643
  simp only [CollatzResearch.WordTrace]
  refine ⟨105029208706552689715003583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70019472471035126476669055 105029208706552689715003583)
  ·
    refine ⟨157543813059829034572505375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105029208706552689715003583 157543813059829034572505375)
    ·
      refine ⟨236315719589743551858758063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157543813059829034572505375 236315719589743551858758063)
      ·
        refine ⟨354473579384615327788137095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236315719589743551858758063 354473579384615327788137095)
        ·
          refine ⟨531710369076922991682205643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354473579384615327788137095 531710369076922991682205643)
          ·
            refine ⟨797565553615384487523308465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 531710369076922991682205643 797565553615384487523308465)
            ·
              refine ⟨598174165211538365642481349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 797565553615384487523308465 598174165211538365642481349)
              ·
                refine ⟨112157655977163443557965253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 598174165211538365642481349 112157655977163443557965253)
                ·
                  refine ⟨21029560495718145667118485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112157655977163443557965253 21029560495718145667118485)
                  ·
                    refine ⟨985760648236788078146179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21029560495718145667118485 985760648236788078146179)
                    ·
                      rfl

theorem cell22_2879643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 6].length) (baseStart_2879643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2879643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2879643 prefixEnd_2879643 := by exact prefixLift 2879643
  have htrace : WordTrace (prefixWord ++ tailWord_2879643) baseStart_2879643 baseEnd_2879643 := by
    simpa [prefixWord, tailWord_2879643, baseEnd_2879643] using wordTrace_append hprefix tailTrace_2879643
  have hstable : (prefixWord ++ tailWord_2879643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879643).length < 2 ^ (prefixWord ++ tailWord_2879643).sum := by decide
  have hdescent : baseEnd_2879643 < baseStart_2879643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879675 : List Nat := [1, 1, 1, 1, 1, 2, 7, 3, 5]
def baseStart_2879675 : Nat := 118140960795 + 2879675 * 2 ^ 59
def prefixEnd_2879675 : Nat := 4983230072969 + 3 ^ 40 * 2879675 * 2
def baseEnd_2879675 : Nat := 328590534163583553782027

theorem tailTrace_2879675 : CollatzResearch.WordTrace tailWord_2879675 prefixEnd_2879675 328590534163583553782027 := by
  unfold tailWord_2879675
  simp only [CollatzResearch.WordTrace]
  refine ⟨105030375842436759180168479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70020250561624506120112319 105030375842436759180168479)
  ·
    refine ⟨157545563763655138770252719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105030375842436759180168479 157545563763655138770252719)
    ·
      refine ⟨236318345645482708155379079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157545563763655138770252719 236318345645482708155379079)
      ·
        refine ⟨354477518468224062233068619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236318345645482708155379079 354477518468224062233068619)
        ·
          refine ⟨531716277702336093349602929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354477518468224062233068619 531716277702336093349602929)
          ·
            refine ⟨398787208276752070012202197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 531716277702336093349602929 398787208276752070012202197)
            ·
              refine ⟨9346575193986376640910989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 398787208276752070012202197 9346575193986376640910989)
              ·
                refine ⟨3504965697744891240341621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9346575193986376640910989 3504965697744891240341621)
                ·
                  refine ⟨328590534163583553782027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3504965697744891240341621 328590534163583553782027)
                  ·
                    rfl

theorem cell22_2879675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 3, 5].length) (baseStart_2879675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2879675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2879675 prefixEnd_2879675 := by exact prefixLift 2879675
  have htrace : WordTrace (prefixWord ++ tailWord_2879675) baseStart_2879675 baseEnd_2879675 := by
    simpa [prefixWord, tailWord_2879675, baseEnd_2879675] using wordTrace_append hprefix tailTrace_2879675
  have hstable : (prefixWord ++ tailWord_2879675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879675).length < 2 ^ (prefixWord ++ tailWord_2879675).sum := by decide
  have hdescent : baseEnd_2879675 < baseStart_2879675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879709 : List Nat := [1, 4, 3, 2, 1, 2, 2, 2, 5]
def baseStart_2879709 : Nat := 118140960795 + 2879709 * 2 ^ 59
def prefixEnd_2879709 : Nat := 4983230072969 + 3 ^ 40 * 2879709 * 2
def baseEnd_2879709 : Nat := 328594413795195301998659

theorem tailTrace_2879709 : CollatzResearch.WordTrace tailWord_2879709 prefixEnd_2879709 328594413795195301998659 := by
  unfold tailWord_2879709
  simp only [CollatzResearch.WordTrace]
  refine ⟨105031615924313582986906181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70021077282875721991270787 105031615924313582986906181)
  ·
    refine ⟨19693427985808796810044909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105031615924313582986906181 19693427985808796810044909)
    ·
      refine ⟨7385035494678298803766841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19693427985808796810044909 7385035494678298803766841)
      ·
        refine ⟨5538776621008724102825131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7385035494678298803766841 5538776621008724102825131)
        ·
          refine ⟨8308164931513086154237697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5538776621008724102825131 8308164931513086154237697)
          ·
            refine ⟨6231123698634814615678273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8308164931513086154237697 6231123698634814615678273)
            ·
              refine ⟨4673342773976110961758705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6231123698634814615678273 4673342773976110961758705)
              ·
                refine ⟨3505007080482083221319029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4673342773976110961758705 3505007080482083221319029)
                ·
                  refine ⟨328594413795195301998659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3505007080482083221319029 328594413795195301998659)
                  ·
                    rfl

theorem cell22_2879709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 2, 5].length) (baseStart_2879709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2879709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2879709 prefixEnd_2879709 := by exact prefixLift 2879709
  have htrace : WordTrace (prefixWord ++ tailWord_2879709) baseStart_2879709 baseEnd_2879709 := by
    simpa [prefixWord, tailWord_2879709, baseEnd_2879709] using wordTrace_append hprefix tailTrace_2879709
  have hstable : (prefixWord ++ tailWord_2879709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879709).length < 2 ^ (prefixWord ++ tailWord_2879709).sum := by decide
  have hdescent : baseEnd_2879709 < baseStart_2879709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879752 : List Nat := [2, 1, 3, 2, 3, 1, 2, 2, 1, 5]
def baseStart_2879752 : Nat := 118140960795 + 2879752 * 2 ^ 59
def prefixEnd_2879752 : Nat := 4983230072969 + 3 ^ 40 * 2879752 * 2
def baseEnd_2879752 : Nat := 985797961164348127170845

theorem tailTrace_2879752 : CollatzResearch.WordTrace tailWord_2879752 prefixEnd_2879752 985797961164348127170845 := by
  unfold tailWord_2879752
  simp only [CollatzResearch.WordTrace]
  refine ⟨52516592131578900665360755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70022122842105200887147673 52516592131578900665360755)
  ·
    refine ⟨78774888197368350998041133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52516592131578900665360755 78774888197368350998041133)
    ·
      refine ⟨29540583074013131624265425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78774888197368350998041133 29540583074013131624265425)
      ·
        refine ⟨22155437305509848718199069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29540583074013131624265425 22155437305509848718199069)
        ·
          refine ⟨8308288989566193269324651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22155437305509848718199069 8308288989566193269324651)
          ·
            refine ⟨12462433484349289903986977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8308288989566193269324651 12462433484349289903986977)
            ·
              refine ⟨9346825113261967427990233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12462433484349289903986977 9346825113261967427990233)
              ·
                refine ⟨7010118834946475570992675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9346825113261967427990233 7010118834946475570992675)
                ·
                  refine ⟨10515178252419713356489013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7010118834946475570992675 10515178252419713356489013)
                  ·
                    refine ⟨985797961164348127170845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10515178252419713356489013 985797961164348127170845)
                    ·
                      rfl

theorem cell22_2879752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_2879752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2879752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2879752 prefixEnd_2879752 := by exact prefixLift 2879752
  have htrace : WordTrace (prefixWord ++ tailWord_2879752) baseStart_2879752 baseEnd_2879752 := by
    simpa [prefixWord, tailWord_2879752, baseEnd_2879752] using wordTrace_append hprefix tailTrace_2879752
  have hstable : (prefixWord ++ tailWord_2879752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879752).length < 2 ^ (prefixWord ++ tailWord_2879752).sum := by decide
  have hdescent : baseEnd_2879752 < baseStart_2879752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879786 : List Nat := [3, 1, 4, 2, 2, 2, 1, 1, 1, 5]
def baseStart_2879786 : Nat := 118140960795 + 2879786 * 2 ^ 59
def prefixEnd_2879786 : Nat := 4983230072969 + 3 ^ 40 * 2879786 * 2
def baseEnd_2879786 : Nat := 985809600059183371820741

theorem tailTrace_2879786 : CollatzResearch.WordTrace tailWord_2879786 prefixEnd_2879786 985809600059183371820741 := by
  unfold tailWord_2879786
  simp only [CollatzResearch.WordTrace]
  refine ⟨26258606086258656284364803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70022949563356416758306141 26258606086258656284364803)
  ·
    refine ⟨39387909129387984426547205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26258606086258656284364803 39387909129387984426547205)
    ·
      refine ⟨7385232961760247079977601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39387909129387984426547205 7385232961760247079977601)
      ·
        refine ⟨5538924721320185309983201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7385232961760247079977601 5538924721320185309983201)
        ·
          refine ⟨4154193540990138982487401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5538924721320185309983201 4154193540990138982487401)
          ·
            refine ⟨3115645155742604236865551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4154193540990138982487401 3115645155742604236865551)
            ·
              refine ⟨4673467733613906355298327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3115645155742604236865551 4673467733613906355298327)
              ·
                refine ⟨7010201600420859532947491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4673467733613906355298327 7010201600420859532947491)
                ·
                  refine ⟨10515302400631289299421237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7010201600420859532947491 10515302400631289299421237)
                  ·
                    refine ⟨985809600059183371820741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10515302400631289299421237 985809600059183371820741)
                    ·
                      rfl

theorem cell22_2879786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_2879786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2879786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2879786 prefixEnd_2879786 := by exact prefixLift 2879786
  have htrace : WordTrace (prefixWord ++ tailWord_2879786) baseStart_2879786 baseEnd_2879786 := by
    simpa [prefixWord, tailWord_2879786, baseEnd_2879786] using wordTrace_append hprefix tailTrace_2879786
  have hstable : (prefixWord ++ tailWord_2879786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879786).length < 2 ^ (prefixWord ++ tailWord_2879786).sum := by decide
  have hdescent : baseEnd_2879786 < baseStart_2879786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879882 : List Nat := [3, 1, 2, 5, 1, 2, 2, 2, 1, 3]
def baseStart_2879882 : Nat := 118140960795 + 2879882 * 2 ^ 59
def prefixEnd_2879882 : Nat := 4983230072969 + 3 ^ 40 * 2879882 * 2
def baseEnd_2879882 : Nat := 985842462821071121420447

theorem tailTrace_2879882 : CollatzResearch.WordTrace tailWord_2879882 prefixEnd_2879882 985842462821071121420447 := by
  unfold tailWord_2879882
  simp only [CollatzResearch.WordTrace]
  refine ⟨26259481438171708383238475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70025283835124555688635933 26259481438171708383238475)
  ·
    refine ⟨39389222157257562574857713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26259481438171708383238475 39389222157257562574857713)
    ·
      refine ⟨29541916617943171931143285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39389222157257562574857713 29541916617943171931143285)
      ·
        refine ⟨2769554682932172368544683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29541916617943171931143285 2769554682932172368544683)
        ·
          refine ⟨4154332024398258552817025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2769554682932172368544683 4154332024398258552817025)
          ·
            refine ⟨3115749018298693914612769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4154332024398258552817025 3115749018298693914612769)
            ·
              refine ⟨2336811763724020435959577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3115749018298693914612769 2336811763724020435959577)
              ·
                refine ⟨1752608822793015326969683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2336811763724020435959577 1752608822793015326969683)
                ·
                  refine ⟨2628913234189522990454525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1752608822793015326969683 2628913234189522990454525)
                  ·
                    refine ⟨985842462821071121420447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2628913234189522990454525 985842462821071121420447)
                    ·
                      rfl

theorem cell22_2879882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 2, 1, 3].length) (baseStart_2879882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2879882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2879882 prefixEnd_2879882 := by exact prefixLift 2879882
  have htrace : WordTrace (prefixWord ++ tailWord_2879882) baseStart_2879882 baseEnd_2879882 := by
    simpa [prefixWord, tailWord_2879882, baseEnd_2879882] using wordTrace_append hprefix tailTrace_2879882
  have hstable : (prefixWord ++ tailWord_2879882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879882).length < 2 ^ (prefixWord ++ tailWord_2879882).sum := by decide
  have hdescent : baseEnd_2879882 < baseStart_2879882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879904 : List Nat := [2, 1, 1, 4, 1, 4, 2, 1, 1, 5]
def baseStart_2879904 : Nat := 118140960795 + 2879904 * 2 ^ 59
def prefixEnd_2879904 : Nat := 4983230072969 + 3 ^ 40 * 2879904 * 2
def baseEnd_2879904 : Nat := 985849993870670397370379

theorem tailTrace_2879904 : CollatzResearch.WordTrace tailWord_2879904 prefixEnd_2879904 985849993870670397370379 := by
  unfold tailWord_2879904
  simp only [CollatzResearch.WordTrace]
  refine ⟨52519364079303565645127383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70025818772404754193503177 52519364079303565645127383)
  ·
    refine ⟨78779046118955348467691075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52519364079303565645127383 78779046118955348467691075)
    ·
      refine ⟨118168569178433022701536613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78779046118955348467691075 118168569178433022701536613)
      ·
        refine ⟨22156606720956191756538115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118168569178433022701536613 22156606720956191756538115)
        ·
          refine ⟨33234910081434287634807173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22156606720956191756538115 33234910081434287634807173)
          ·
            refine ⟨6231545640268928931526345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33234910081434287634807173 6231545640268928931526345)
            ·
              refine ⟨4673659230201696698644759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6231545640268928931526345 4673659230201696698644759)
              ·
                refine ⟨7010488845302545047967139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4673659230201696698644759 7010488845302545047967139)
                ·
                  refine ⟨10515733267953817571950709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7010488845302545047967139 10515733267953817571950709)
                  ·
                    refine ⟨985849993870670397370379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10515733267953817571950709 985849993870670397370379)
                    ·
                      rfl

theorem cell22_2879904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 1, 1, 5].length) (baseStart_2879904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2879904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2879904 prefixEnd_2879904 := by exact prefixLift 2879904
  have htrace : WordTrace (prefixWord ++ tailWord_2879904) baseStart_2879904 baseEnd_2879904 := by
    simpa [prefixWord, tailWord_2879904, baseEnd_2879904] using wordTrace_append hprefix tailTrace_2879904
  have hstable : (prefixWord ++ tailWord_2879904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879904).length < 2 ^ (prefixWord ++ tailWord_2879904).sum := by decide
  have hdescent : baseEnd_2879904 < baseStart_2879904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879925 : List Nat := [1, 3, 3, 2, 4, 1, 2, 1, 1, 4]
def baseStart_2879925 : Nat := 118140960795 + 2879925 * 2 ^ 59
def prefixEnd_2879925 : Nat := 4983230072969 + 3 ^ 40 * 2879925 * 2
def baseEnd_2879925 : Nat := 985857182599833342595315

theorem tailTrace_2879925 : CollatzResearch.WordTrace tailWord_2879925 prefixEnd_2879925 985857182599833342595315 := by
  unfold tailWord_2879925
  simp only [CollatzResearch.WordTrace]
  refine ⟨105039494091531051876769229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70026329394354034584512819 105039494091531051876769229)
  ·
    refine ⟨39389810284324144453788461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105039494091531051876769229 39389810284324144453788461)
    ·
      refine ⟨14771178856621554170170673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39389810284324144453788461 14771178856621554170170673)
      ·
        refine ⟨11078384142466165627628005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14771178856621554170170673 11078384142466165627628005)
        ·
          refine ⟨2077197026712406055180251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11078384142466165627628005 2077197026712406055180251)
          ·
            refine ⟨3115795540068609082770377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2077197026712406055180251 3115795540068609082770377)
            ·
              refine ⟨2336846655051456812077783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3115795540068609082770377 2336846655051456812077783)
              ·
                refine ⟨3505269982577185218116675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2336846655051456812077783 3505269982577185218116675)
                ·
                  refine ⟨5257904973865777827175013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3505269982577185218116675 5257904973865777827175013)
                  ·
                    refine ⟨985857182599833342595315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5257904973865777827175013 985857182599833342595315)
                    ·
                      rfl

theorem cell22_2879925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_2879925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2879925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2879925 prefixEnd_2879925 := by exact prefixLift 2879925
  have htrace : WordTrace (prefixWord ++ tailWord_2879925) baseStart_2879925 baseEnd_2879925 := by
    simpa [prefixWord, tailWord_2879925, baseEnd_2879925] using wordTrace_append hprefix tailTrace_2879925
  have hstable : (prefixWord ++ tailWord_2879925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879925).length < 2 ^ (prefixWord ++ tailWord_2879925).sum := by decide
  have hdescent : baseEnd_2879925 < baseStart_2879925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2879977 : List Nat := [1, 2, 1, 1, 1, 2, 1, 4, 4, 5]
def baseStart_2879977 : Nat := 118140960795 + 2879977 * 2 ^ 59
def prefixEnd_2879977 : Nat := 4983230072969 + 3 ^ 40 * 2879977 * 2
def baseEnd_2879977 : Nat := 985874983262522540295155

theorem tailTrace_2879977 : CollatzResearch.WordTrace tailWord_2879977 prefixEnd_2879977 985874983262522540295155 := by
  unfold tailWord_2879977
  simp only [CollatzResearch.WordTrace]
  refine ⟨105041390687342664757662185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70027593791561776505108123 105041390687342664757662185)
  ·
    refine ⟨78781043015506998568246639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105041390687342664757662185 78781043015506998568246639)
    ·
      refine ⟨118171564523260497852369959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78781043015506998568246639 118171564523260497852369959)
      ·
        refine ⟨177257346784890746778554939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118171564523260497852369959 177257346784890746778554939)
        ·
          refine ⟨265886020177336120167832409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177257346784890746778554939 265886020177336120167832409)
          ·
            refine ⟨199414515133002090125874307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265886020177336120167832409 199414515133002090125874307)
            ·
              refine ⟨299121772699503135188811461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199414515133002090125874307 299121772699503135188811461)
              ·
                refine ⟨56085332381156837847902149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 299121772699503135188811461 56085332381156837847902149)
                ·
                  refine ⟨10515999821466907096481653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56085332381156837847902149 10515999821466907096481653)
                  ·
                    refine ⟨985874983262522540295155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10515999821466907096481653 985874983262522540295155)
                    ·
                      rfl

theorem cell22_2879977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 5].length) (baseStart_2879977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2879977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2879977 prefixEnd_2879977 := by exact prefixLift 2879977
  have htrace : WordTrace (prefixWord ++ tailWord_2879977) baseStart_2879977 baseEnd_2879977 := by
    simpa [prefixWord, tailWord_2879977, baseEnd_2879977] using wordTrace_append hprefix tailTrace_2879977
  have hstable : (prefixWord ++ tailWord_2879977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2879977).length < 2 ^ (prefixWord ++ tailWord_2879977).sum := by decide
  have hdescent : baseEnd_2879977 < baseStart_2879977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2879977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880026 : List Nat := [3, 1, 1, 3, 1, 1, 5, 2, 1, 4]
def baseStart_2880026 : Nat := 118140960795 + 2880026 * 2 ^ 59
def prefixEnd_2880026 : Nat := 4983230072969 + 3 ^ 40 * 2880026 * 2
def baseEnd_2880026 : Nat := 985891756963902745820005

theorem tailTrace_2880026 : CollatzResearch.WordTrace tailWord_2880026 prefixEnd_2880026 985891756963902745820005 := by
  unfold tailWord_2880026
  simp only [CollatzResearch.WordTrace]
  refine ⟨26260794466041286531548983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70028785242776764084130621 26260794466041286531548983)
  ·
    refine ⟨39391191699061929797323475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26260794466041286531548983 39391191699061929797323475)
    ·
      refine ⟨59086787548592894695985213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39391191699061929797323475 59086787548592894695985213)
      ·
        refine ⟨22157545330722335510994455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59086787548592894695985213 22157545330722335510994455)
        ·
          refine ⟨33236317996083503266491683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22157545330722335510994455 33236317996083503266491683)
          ·
            refine ⟨49854476994125254899737525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33236317996083503266491683 49854476994125254899737525)
            ·
              refine ⟨4673857218199242646850393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49854476994125254899737525 4673857218199242646850393)
              ·
                refine ⟨3505392913649431985137795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4673857218199242646850393 3505392913649431985137795)
                ·
                  refine ⟨5258089370474147977706693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3505392913649431985137795 5258089370474147977706693)
                  ·
                    refine ⟨985891756963902745820005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5258089370474147977706693 985891756963902745820005)
                    ·
                      rfl

theorem cell22_2880026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 2, 1, 4].length) (baseStart_2880026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2880026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2880026 prefixEnd_2880026 := by exact prefixLift 2880026
  have htrace : WordTrace (prefixWord ++ tailWord_2880026) baseStart_2880026 baseEnd_2880026 := by
    simpa [prefixWord, tailWord_2880026, baseEnd_2880026] using wordTrace_append hprefix tailTrace_2880026
  have hstable : (prefixWord ++ tailWord_2880026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880026).length < 2 ^ (prefixWord ++ tailWord_2880026).sum := by decide
  have hdescent : baseEnd_2880026 < baseStart_2880026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880058 : List Nat := [3, 1, 1, 1, 3, 3, 4, 2, 4]
def baseStart_2880058 : Nat := 118140960795 + 2880058 * 2 ^ 59
def prefixEnd_2880058 : Nat := 4983230072969 + 3 ^ 40 * 2880058 * 2
def baseEnd_2880058 : Nat := 328634237072621776339969

theorem tailTrace_2880058 : CollatzResearch.WordTrace tailWord_2880058 prefixEnd_2880058 328634237072621776339969 := by
  unfold tailWord_2880058
  simp only [CollatzResearch.WordTrace]
  refine ⟨26261086250012303897840207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70029563333366143727573885 26261086250012303897840207)
  ·
    refine ⟨39391629375018455846760311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26261086250012303897840207 39391629375018455846760311)
    ·
      refine ⟨59087444062527683770140467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39391629375018455846760311 59087444062527683770140467)
      ·
        refine ⟨88631166093791525655210701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59087444062527683770140467 88631166093791525655210701)
        ·
          refine ⟨33236687285171822120704013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88631166093791525655210701 33236687285171822120704013)
          ·
            refine ⟨12463757731939433295264005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33236687285171822120704013 12463757731939433295264005)
            ·
              refine ⟨2336954574738643742862001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12463757731939433295264005 2336954574738643742862001)
              ·
                refine ⟨1752715931053982807146501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2336954574738643742862001 1752715931053982807146501)
                ·
                  refine ⟨328634237072621776339969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1752715931053982807146501 328634237072621776339969)
                  ·
                    rfl

theorem cell22_2880058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 2, 4].length) (baseStart_2880058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2880058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2880058 prefixEnd_2880058 := by exact prefixLift 2880058
  have htrace : WordTrace (prefixWord ++ tailWord_2880058) baseStart_2880058 baseEnd_2880058 := by
    simpa [prefixWord, tailWord_2880058, baseEnd_2880058] using wordTrace_append hprefix tailTrace_2880058
  have hstable : (prefixWord ++ tailWord_2880058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880058).length < 2 ^ (prefixWord ++ tailWord_2880058).sum := by decide
  have hdescent : baseEnd_2880058 < baseStart_2880058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880069 : List Nat := [1, 3, 1, 1, 1, 5, 3, 7]
def baseStart_2880069 : Nat := 118140960795 + 2880069 * 2 ^ 59
def prefixEnd_2880069 : Nat := 4983230072969 + 3 ^ 40 * 2880069 * 2
def baseEnd_2880069 : Nat := 109545164082518329666097

theorem tailTrace_2880069 : CollatzResearch.WordTrace tailWord_2880069 prefixEnd_2880069 109545164082518329666097 := by
  unfold tailWord_2880069
  simp only [CollatzResearch.WordTrace]
  refine ⟨105044746203009364470011261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70029830802006242980007507 105044746203009364470011261)
  ·
    refine ⟨39391779826128511676254223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105044746203009364470011261 39391779826128511676254223)
    ·
      refine ⟨59087669739192767514381335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39391779826128511676254223 59087669739192767514381335)
      ·
        refine ⟨88631504608789151271572003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59087669739192767514381335 88631504608789151271572003)
        ·
          refine ⟨132947256913183726907358005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88631504608789151271572003 132947256913183726907358005)
          ·
            refine ⟨12463805335610974397564813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 132947256913183726907358005 12463805335610974397564813)
            ·
              refine ⟨4673927000854115399086805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12463805335610974397564813 4673927000854115399086805)
              ·
                refine ⟨109545164082518329666097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4673927000854115399086805 109545164082518329666097)
                ·
                  rfl

theorem cell22_2880069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 7].length) (baseStart_2880069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2880069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2880069 prefixEnd_2880069 := by exact prefixLift 2880069
  have htrace : WordTrace (prefixWord ++ tailWord_2880069) baseStart_2880069 baseEnd_2880069 := by
    simpa [prefixWord, tailWord_2880069, baseEnd_2880069] using wordTrace_append hprefix tailTrace_2880069
  have hstable : (prefixWord ++ tailWord_2880069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880069).length < 2 ^ (prefixWord ++ tailWord_2880069).sum := by decide
  have hdescent : baseEnd_2880069 < baseStart_2880069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880212 : List Nat := [2, 4, 1, 3, 2, 1, 3, 1, 1, 4]
def baseStart_2880212 : Nat := 118140960795 + 2880212 * 2 ^ 59
def prefixEnd_2880212 : Nat := 4983230072969 + 3 ^ 40 * 2880212 * 2
def baseEnd_2880212 : Nat := 985955428565060260669435

theorem tailTrace_2880212 : CollatzResearch.WordTrace tailWord_2880212 prefixEnd_2880212 985955428565060260669435 := by
  unfold tailWord_2880212
  simp only [CollatzResearch.WordTrace]
  refine ⟨52524980920745649946233445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70033307894327533261644593 52524980920745649946233445)
  ·
    refine ⟨9848433922639809364918771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52524980920745649946233445 9848433922639809364918771)
    ·
      refine ⟨14772650883959714047378157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9848433922639809364918771 14772650883959714047378157)
      ·
        refine ⟨5539744081484892767766809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14772650883959714047378157 5539744081484892767766809)
        ·
          refine ⟨4154808061113669575825107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5539744081484892767766809 4154808061113669575825107)
          ·
            refine ⟨6232212091670504363737661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4154808061113669575825107 6232212091670504363737661)
            ·
              refine ⟨2337079534376439136401623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6232212091670504363737661 2337079534376439136401623)
              ·
                refine ⟨3505619301564658704602435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2337079534376439136401623 3505619301564658704602435)
                ·
                  refine ⟨5258428952346988056903653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3505619301564658704602435 5258428952346988056903653)
                  ·
                    refine ⟨985955428565060260669435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5258428952346988056903653 985955428565060260669435)
                    ·
                      rfl

theorem cell22_2880212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_2880212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2880212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2880212 prefixEnd_2880212 := by exact prefixLift 2880212
  have htrace : WordTrace (prefixWord ++ tailWord_2880212) baseStart_2880212 baseEnd_2880212 := by
    simpa [prefixWord, tailWord_2880212, baseEnd_2880212] using wordTrace_append hprefix tailTrace_2880212
  have hstable : (prefixWord ++ tailWord_2880212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880212).length < 2 ^ (prefixWord ++ tailWord_2880212).sum := by decide
  have hdescent : baseEnd_2880212 < baseStart_2880212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880219 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 3, 9]
def baseStart_2880219 : Nat := 118140960795 + 2880219 * 2 ^ 59
def prefixEnd_2880219 : Nat := 4983230072969 + 3 ^ 40 * 2880219 * 2
def baseEnd_2880219 : Nat := 985957824808114575744413

theorem tailTrace_2880219 : CollatzResearch.WordTrace tailWord_2880219 prefixEnd_2880219 985957824808114575744413 := by
  unfold tailWord_2880219
  simp only [CollatzResearch.WordTrace]
  refine ⟨105050217152465940087971711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70033478101643960058647807 105050217152465940087971711)
  ·
    refine ⟨157575325728698910131957567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105050217152465940087971711 157575325728698910131957567)
    ·
      refine ⟨236362988593048365197936351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157575325728698910131957567 236362988593048365197936351)
      ·
        refine ⟨354544482889572547796904527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236362988593048365197936351 354544482889572547796904527)
        ·
          refine ⟨531816724334358821695356791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354544482889572547796904527 531816724334358821695356791)
          ·
            refine ⟨797725086501538232543035187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 531816724334358821695356791 797725086501538232543035187)
            ·
              refine ⟨1196587629752307348814552781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 797725086501538232543035187 1196587629752307348814552781)
              ·
                refine ⟨448720361157115255805457293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1196587629752307348814552781 448720361157115255805457293)
                ·
                  refine ⟨168270135433918220927046485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 448720361157115255805457293 168270135433918220927046485)
                  ·
                    refine ⟨985957824808114575744413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 168270135433918220927046485 985957824808114575744413)
                    ·
                      rfl

theorem cell22_2880219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 9].length) (baseStart_2880219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2880219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2880219 prefixEnd_2880219 := by exact prefixLift 2880219
  have htrace : WordTrace (prefixWord ++ tailWord_2880219) baseStart_2880219 baseEnd_2880219 := by
    simpa [prefixWord, tailWord_2880219, baseEnd_2880219] using wordTrace_append hprefix tailTrace_2880219
  have hstable : (prefixWord ++ tailWord_2880219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880219).length < 2 ^ (prefixWord ++ tailWord_2880219).sum := by decide
  have hdescent : baseEnd_2880219 < baseStart_2880219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880225 : List Nat := [1, 2, 3, 1, 4, 2, 2, 2, 2, 3]
def baseStart_2880225 : Nat := 118140960795 + 2880225 * 2 ^ 59
def prefixEnd_2880225 : Nat := 4983230072969 + 3 ^ 40 * 2880225 * 2
def baseEnd_2880225 : Nat := 985959878730732560094395

theorem tailTrace_2880225 : CollatzResearch.WordTrace tailWord_2880225 prefixEnd_2880225 985959878730732560094395 := by
  unfold tailWord_2880225
  simp only [CollatzResearch.WordTrace]
  refine ⟨105050435990444203112690129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70033623993629468741793419 105050435990444203112690129)
  ·
    refine ⟨78787826992833152334517597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105050435990444203112690129 78787826992833152334517597)
    ·
      refine ⟨29545435122312432125444099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78787826992833152334517597 29545435122312432125444099)
      ·
        refine ⟨44318152683468648188166149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29545435122312432125444099 44318152683468648188166149)
        ·
          refine ⟨8309653628150371535281153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44318152683468648188166149 8309653628150371535281153)
          ·
            refine ⟨6232240221112778651460865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8309653628150371535281153 6232240221112778651460865)
            ·
              refine ⟨4674180165834583988595649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6232240221112778651460865 4674180165834583988595649)
              ·
                refine ⟨3505635124375937991446737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4674180165834583988595649 3505635124375937991446737)
                ·
                  refine ⟨2629226343281953493585053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3505635124375937991446737 2629226343281953493585053)
                  ·
                    refine ⟨985959878730732560094395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2629226343281953493585053 985959878730732560094395)
                    ·
                      rfl

theorem cell22_2880225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 2, 2, 3].length) (baseStart_2880225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2880225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2880225 prefixEnd_2880225 := by exact prefixLift 2880225
  have htrace : WordTrace (prefixWord ++ tailWord_2880225) baseStart_2880225 baseEnd_2880225 := by
    simpa [prefixWord, tailWord_2880225, baseEnd_2880225] using wordTrace_append hprefix tailTrace_2880225
  have hstable : (prefixWord ++ tailWord_2880225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880225).length < 2 ^ (prefixWord ++ tailWord_2880225).sum := by decide
  have hdescent : baseEnd_2880225 < baseStart_2880225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880227 : List Nat := [1, 1, 1, 7, 1, 3, 2, 2, 4]
def baseStart_2880227 : Nat := 118140960795 + 2880227 * 2 ^ 59
def prefixEnd_2880227 : Nat := 4983230072969 + 3 ^ 40 * 2880227 * 2
def baseEnd_2880227 : Nat := 328653521123868407181463

theorem tailTrace_2880227 : CollatzResearch.WordTrace tailWord_2880227 prefixEnd_2880227 328653521123868407181463 := by
  unfold tailWord_2880227
  simp only [CollatzResearch.WordTrace]
  refine ⟨105050508936436957454262935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70033672624291304969508623 105050508936436957454262935)
  ·
    refine ⟨157575763404655436181394403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105050508936436957454262935 157575763404655436181394403)
    ·
      refine ⟨236363645106983154272091605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157575763404655436181394403 236363645106983154272091605)
      ·
        refine ⟨5539772932194917678252147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 236363645106983154272091605 5539772932194917678252147)
        ·
          refine ⟨8309659398292376517378221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5539772932194917678252147 8309659398292376517378221)
          ·
            refine ⟨3116122274359641194016833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8309659398292376517378221 3116122274359641194016833)
            ·
              refine ⟨2337091705769730895512625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3116122274359641194016833 2337091705769730895512625)
              ·
                refine ⟨1752818779327298171634469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2337091705769730895512625 1752818779327298171634469)
                ·
                  refine ⟨328653521123868407181463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1752818779327298171634469 328653521123868407181463)
                  ·
                    rfl

theorem cell22_2880227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 2, 4].length) (baseStart_2880227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2880227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2880227 prefixEnd_2880227 := by exact prefixLift 2880227
  have htrace : WordTrace (prefixWord ++ tailWord_2880227) baseStart_2880227 baseEnd_2880227 := by
    simpa [prefixWord, tailWord_2880227, baseEnd_2880227] using wordTrace_append hprefix tailTrace_2880227
  have hstable : (prefixWord ++ tailWord_2880227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880227).length < 2 ^ (prefixWord ++ tailWord_2880227).sum := by decide
  have hdescent : baseEnd_2880227 < baseStart_2880227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880238 : List Nat := [4, 1, 2, 1, 1, 5, 1, 7]
def baseStart_2880238 : Nat := 118140960795 + 2880238 * 2 ^ 59
def prefixEnd_2880238 : Nat := 4983230072969 + 3 ^ 40 * 2880238 * 2
def baseEnd_2880238 : Nat := 109551592099600539946595

theorem tailTrace_2880238 : CollatzResearch.WordTrace tailWord_2880238 prefixEnd_2880238 109551592099600539946595 := by
  unfold tailWord_2880238
  simp only [CollatzResearch.WordTrace]
  refine ⟨13131363767424638291614171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70033940092931404221942245 13131363767424638291614171)
  ·
    refine ⟨19697045651136957437421257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13131363767424638291614171 19697045651136957437421257)
    ·
      refine ⟨14772784238352718078065943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19697045651136957437421257 14772784238352718078065943)
      ·
        refine ⟨22159176357529077117098915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14772784238352718078065943 22159176357529077117098915)
        ·
          refine ⟨33238764536293615675648373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22159176357529077117098915 33238764536293615675648373)
          ·
            refine ⟨3116134175277526469592035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33238764536293615675648373 3116134175277526469592035)
            ·
              refine ⟨4674201262916289704388053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3116134175277526469592035 4674201262916289704388053)
              ·
                refine ⟨109551592099600539946595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4674201262916289704388053 109551592099600539946595)
                ·
                  rfl

theorem cell22_2880238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 7].length) (baseStart_2880238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2880238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2880238 prefixEnd_2880238 := by exact prefixLift 2880238
  have htrace : WordTrace (prefixWord ++ tailWord_2880238) baseStart_2880238 baseEnd_2880238 := by
    simpa [prefixWord, tailWord_2880238, baseEnd_2880238] using wordTrace_append hprefix tailTrace_2880238
  have hstable : (prefixWord ++ tailWord_2880238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880238).length < 2 ^ (prefixWord ++ tailWord_2880238).sum := by decide
  have hdescent : baseEnd_2880238 < baseStart_2880238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880253 : List Nat := [1, 4, 1, 1, 1, 1, 5, 2, 3, 3]
def baseStart_2880253 : Nat := 118140960795 + 2880253 * 2 ^ 59
def prefixEnd_2880253 : Nat := 4983230072969 + 3 ^ 40 * 2880253 * 2
def baseEnd_2880253 : Nat := 985969463702949820394309

theorem tailTrace_2880253 : CollatzResearch.WordTrace tailWord_2880253 prefixEnd_2880253 985969463702949820394309 := by
  unfold tailWord_2880253
  simp only [CollatzResearch.WordTrace]
  refine ⟨105051457234342763894709413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70034304822895175929806275 105051457234342763894709413)
  ·
    refine ⟨19697148231439268230258015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105051457234342763894709413 19697148231439268230258015)
    ·
      refine ⟨29545722347158902345387023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19697148231439268230258015 29545722347158902345387023)
      ·
        refine ⟨44318583520738353518080535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29545722347158902345387023 44318583520738353518080535)
        ·
          refine ⟨66477875281107530277120803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44318583520738353518080535 66477875281107530277120803)
          ·
            refine ⟨99716812921661295415681205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66477875281107530277120803 99716812921661295415681205)
            ·
              refine ⟨9348451211405746445220113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 99716812921661295415681205 9348451211405746445220113)
              ·
                refine ⟨7011338408554309833915085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9348451211405746445220113 7011338408554309833915085)
                ·
                  refine ⟨2629251903207866187718157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7011338408554309833915085 2629251903207866187718157)
                  ·
                    refine ⟨985969463702949820394309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2629251903207866187718157 985969463702949820394309)
                    ·
                      rfl

theorem cell22_2880253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 3, 3].length) (baseStart_2880253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2880253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2880253 prefixEnd_2880253 := by exact prefixLift 2880253
  have htrace : WordTrace (prefixWord ++ tailWord_2880253) baseStart_2880253 baseEnd_2880253 := by
    simpa [prefixWord, tailWord_2880253, baseEnd_2880253] using wordTrace_append hprefix tailTrace_2880253
  have hstable : (prefixWord ++ tailWord_2880253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880253).length < 2 ^ (prefixWord ++ tailWord_2880253).sum := by decide
  have hdescent : baseEnd_2880253 < baseStart_2880253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880266 : List Nat := [3, 1, 2, 2, 1, 2, 2, 2, 7]
def baseStart_2880266 : Nat := 118140960795 + 2880266 * 2 ^ 59
def prefixEnd_2880266 : Nat := 4983230072969 + 3 ^ 40 * 2880266 * 2
def baseEnd_2880266 : Nat := 328657971289540706606423

theorem tailTrace_2880266 : CollatzResearch.WordTrace tailWord_2880266 prefixEnd_2880266 328657971289540706606423 := by
  unfold tailWord_2880266
  simp only [CollatzResearch.WordTrace]
  refine ⟨26262982845823916778733163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70034620922197111409955101 26262982845823916778733163)
  ·
    refine ⟨39394474268735875168099745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26262982845823916778733163 39394474268735875168099745)
    ·
      refine ⟨29545855701551906376074809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39394474268735875168099745 29545855701551906376074809)
      ·
        refine ⟨22159391776163929782056107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29545855701551906376074809 22159391776163929782056107)
        ·
          refine ⟨33239087664245894673084161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22159391776163929782056107 33239087664245894673084161)
          ·
            refine ⟨24929315748184421004813121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33239087664245894673084161 24929315748184421004813121)
            ·
              refine ⟨18696986811138315753609841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24929315748184421004813121 18696986811138315753609841)
              ·
                refine ⟨14022740108353736815207381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18696986811138315753609841 14022740108353736815207381)
                ·
                  refine ⟨328657971289540706606423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14022740108353736815207381 328657971289540706606423)
                  ·
                    rfl

theorem cell22_2880266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 7].length) (baseStart_2880266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2880266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2880266 prefixEnd_2880266 := by exact prefixLift 2880266
  have htrace : WordTrace (prefixWord ++ tailWord_2880266) baseStart_2880266 baseEnd_2880266 := by
    simpa [prefixWord, tailWord_2880266, baseEnd_2880266] using wordTrace_append hprefix tailTrace_2880266
  have hstable : (prefixWord ++ tailWord_2880266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880266).length < 2 ^ (prefixWord ++ tailWord_2880266).sum := by decide
  have hdescent : baseEnd_2880266 < baseStart_2880266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880311 : List Nat := [1, 1, 3, 1, 2, 1, 3, 4, 6]
def baseStart_2880311 : Nat := 118140960795 + 2880311 * 2 ^ 59
def prefixEnd_2880311 : Nat := 4983230072969 + 3 ^ 40 * 2880311 * 2
def baseEnd_2880311 : Nat := 328663106096085667481377

theorem tailTrace_2880311 : CollatzResearch.WordTrace tailWord_2880311 prefixEnd_2880311 328663106096085667481377 := by
  unfold tailWord_2880311
  simp only [CollatzResearch.WordTrace]
  refine ⟨105053572668132639800320787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70035715112088426533547191 105053572668132639800320787)
  ·
    refine ⟨157580359002198959700481181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105053572668132639800320787 157580359002198959700481181)
    ·
      refine ⟨59092634625824609887680443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157580359002198959700481181 59092634625824609887680443)
      ·
        refine ⟨88638951938736914831520665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59092634625824609887680443 88638951938736914831520665)
        ·
          refine ⟨66479213954052686123640499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88638951938736914831520665 66479213954052686123640499)
          ·
            refine ⟨99718820931079029185460749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66479213954052686123640499 99718820931079029185460749)
            ·
              refine ⟨37394557849154635944547781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99718820931079029185460749 37394557849154635944547781)
              ·
                refine ⟨7011479596716494239602709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37394557849154635944547781 7011479596716494239602709)
                ·
                  refine ⟨328663106096085667481377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7011479596716494239602709 328663106096085667481377)
                  ·
                    rfl

theorem cell22_2880311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 6].length) (baseStart_2880311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2880311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2880311 prefixEnd_2880311 := by exact prefixLift 2880311
  have htrace : WordTrace (prefixWord ++ tailWord_2880311) baseStart_2880311 baseEnd_2880311 := by
    simpa [prefixWord, tailWord_2880311, baseEnd_2880311] using wordTrace_append hprefix tailTrace_2880311
  have hstable : (prefixWord ++ tailWord_2880311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880311).length < 2 ^ (prefixWord ++ tailWord_2880311).sum := by decide
  have hdescent : baseEnd_2880311 < baseStart_2880311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880321 : List Nat := [1, 2, 5, 3, 1, 2, 1, 3, 1, 3]
def baseStart_2880321 : Nat := 118140960795 + 2880321 * 2 ^ 59
def prefixEnd_2880321 : Nat := 4983230072969 + 3 ^ 40 * 2880321 * 2
def baseEnd_2880321 : Nat := 985992741492620309694101

theorem tailTrace_2880321 : CollatzResearch.WordTrace tailWord_2880321 prefixEnd_2880321 985992741492620309694101 := by
  unfold tailWord_2880321
  simp only [CollatzResearch.WordTrace]
  refine ⟨105053937398096411508184817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70035958265397607672123211 105053937398096411508184817)
  ·
    refine ⟨78790453048572308631138613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105053937398096411508184817 78790453048572308631138613)
    ·
      refine ⟨7386604973303653934169245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78790453048572308631138613 7386604973303653934169245)
      ·
        refine ⟨2769976864988870225313467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7386604973303653934169245 2769976864988870225313467)
        ·
          refine ⟨4154965297483305337970201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2769976864988870225313467 4154965297483305337970201)
          ·
            refine ⟨3116223973112479003477651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4154965297483305337970201 3116223973112479003477651)
            ·
              refine ⟨4674335959668718505216477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3116223973112479003477651 4674335959668718505216477)
              ·
                refine ⟨1752875984875769439456179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4674335959668718505216477 1752875984875769439456179)
                ·
                  refine ⟨2629313977313654159184269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1752875984875769439456179 2629313977313654159184269)
                  ·
                    refine ⟨985992741492620309694101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2629313977313654159184269 985992741492620309694101)
                    ·
                      rfl

theorem cell22_2880321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_2880321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2880321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2880321 prefixEnd_2880321 := by exact prefixLift 2880321
  have htrace : WordTrace (prefixWord ++ tailWord_2880321) baseStart_2880321 baseEnd_2880321 := by
    simpa [prefixWord, tailWord_2880321, baseEnd_2880321] using wordTrace_append hprefix tailTrace_2880321
  have hstable : (prefixWord ++ tailWord_2880321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880321).length < 2 ^ (prefixWord ++ tailWord_2880321).sum := by decide
  have hdescent : baseEnd_2880321 < baseStart_2880321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880371 : List Nat := [1, 1, 1, 2, 2, 1, 4, 1, 2, 7]
def baseStart_2880371 : Nat := 118140960795 + 2880371 * 2 ^ 59
def prefixEnd_2880371 : Nat := 4983230072969 + 3 ^ 40 * 2880371 * 2
def baseEnd_2880371 : Nat := 986009857514436845943947

theorem tailTrace_2880371 : CollatzResearch.WordTrace tailWord_2880371 prefixEnd_2880371 986009857514436845943947 := by
  unfold tailWord_2880371
  simp only [CollatzResearch.WordTrace]
  refine ⟨105055761047915270047504967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70037174031943513365003311 105055761047915270047504967)
  ·
    refine ⟨157583641571872905071257451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105055761047915270047504967 157583641571872905071257451)
    ·
      refine ⟨236375462357809357606886177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157583641571872905071257451 236375462357809357606886177)
      ·
        refine ⟨177281596768357018205164633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236375462357809357606886177 177281596768357018205164633)
        ·
          refine ⟨132961197576267763653873475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177281596768357018205164633 132961197576267763653873475)
          ·
            refine ⟨199441796364401645480810213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132961197576267763653873475 199441796364401645480810213)
            ·
              refine ⟨37395336818325308527651915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 199441796364401645480810213 37395336818325308527651915)
              ·
                refine ⟨56093005227487962791477873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37395336818325308527651915 56093005227487962791477873)
                ·
                  refine ⟨42069753920615972093608405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56093005227487962791477873 42069753920615972093608405)
                  ·
                    refine ⟨986009857514436845943947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42069753920615972093608405 986009857514436845943947)
                    ·
                      rfl

theorem cell22_2880371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 7].length) (baseStart_2880371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2880371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2880371 prefixEnd_2880371 := by exact prefixLift 2880371
  have htrace : WordTrace (prefixWord ++ tailWord_2880371) baseStart_2880371 baseEnd_2880371 := by
    simpa [prefixWord, tailWord_2880371, baseEnd_2880371] using wordTrace_append hprefix tailTrace_2880371
  have hstable : (prefixWord ++ tailWord_2880371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880371).length < 2 ^ (prefixWord ++ tailWord_2880371).sum := by decide
  have hdescent : baseEnd_2880371 < baseStart_2880371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880373 : List Nat := [1, 3, 4, 1, 1, 2, 2, 8]
def baseStart_2880373 : Nat := 118140960795 + 2880373 * 2 ^ 59
def prefixEnd_2880373 : Nat := 4983230072969 + 3 ^ 40 * 2880373 * 2
def baseEnd_2880373 : Nat := 109556726906145500821549

theorem tailTrace_2880373 : CollatzResearch.WordTrace tailWord_2880373 prefixEnd_2880373 109556726906145500821549 := by
  unfold tailWord_2880373
  simp only [CollatzResearch.WordTrace]
  refine ⟨105055833993908024389077773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70037222662605349592718515 105055833993908024389077773)
  ·
    refine ⟨39395937747715509145904165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105055833993908024389077773 39395937747715509145904165)
    ·
      refine ⟨7386738327696657964857031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39395937747715509145904165 7386738327696657964857031)
      ·
        refine ⟨11080107491544986947285547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7386738327696657964857031 11080107491544986947285547)
        ·
          refine ⟨16620161237317480420928321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11080107491544986947285547 16620161237317480420928321)
          ·
            refine ⟨12465120927988110315696241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16620161237317480420928321 12465120927988110315696241)
            ·
              refine ⟨9348840695991082736772181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12465120927988110315696241 9348840695991082736772181)
              ·
                refine ⟨109556726906145500821549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9348840695991082736772181 109556726906145500821549)
                ·
                  rfl

theorem cell22_2880373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 8].length) (baseStart_2880373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2880373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2880373 prefixEnd_2880373 := by exact prefixLift 2880373
  have htrace : WordTrace (prefixWord ++ tailWord_2880373) baseStart_2880373 baseEnd_2880373 := by
    simpa [prefixWord, tailWord_2880373, baseEnd_2880373] using wordTrace_append hprefix tailTrace_2880373
  have hstable : (prefixWord ++ tailWord_2880373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880373).length < 2 ^ (prefixWord ++ tailWord_2880373).sum := by decide
  have hdescent : baseEnd_2880373 < baseStart_2880373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880452 : List Nat := [2, 3, 3, 3, 1, 1, 1, 1, 7]
def baseStart_2880452 : Nat := 118140960795 + 2880452 * 2 ^ 59
def prefixEnd_2880452 : Nat := 4983230072969 + 3 ^ 40 * 2880452 * 2
def baseEnd_2880452 : Nat := 328679195156593211556233

theorem tailTrace_2880452 : CollatzResearch.WordTrace tailWord_2880452 prefixEnd_2880452 328679195156593211556233 := by
  unfold tailWord_2880452
  simp only [CollatzResearch.WordTrace]
  refine ⟨52529357680310910440601805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70039143573747880587469073 52529357680310910440601805)
  ·
    refine ⟨19698509130116591415225677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52529357680310910440601805 19698509130116591415225677)
    ·
      refine ⟨7386940923793721780709629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19698509130116591415225677 7386940923793721780709629)
      ·
        refine ⟨2770102846422645667766111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7386940923793721780709629 2770102846422645667766111)
        ·
          refine ⟨4155154269633968501649167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2770102846422645667766111 4155154269633968501649167)
          ·
            refine ⟨6232731404450952752473751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4155154269633968501649167 6232731404450952752473751)
            ·
              refine ⟨9349097106676429128710627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6232731404450952752473751 9349097106676429128710627)
              ·
                refine ⟨14023645660014643693065941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9349097106676429128710627 14023645660014643693065941)
                ·
                  refine ⟨328679195156593211556233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14023645660014643693065941 328679195156593211556233)
                  ·
                    rfl

theorem cell22_2880452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 7].length) (baseStart_2880452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2880452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2880452 prefixEnd_2880452 := by exact prefixLift 2880452
  have htrace : WordTrace (prefixWord ++ tailWord_2880452) baseStart_2880452 baseEnd_2880452 := by
    simpa [prefixWord, tailWord_2880452, baseEnd_2880452] using wordTrace_append hprefix tailTrace_2880452
  have hstable : (prefixWord ++ tailWord_2880452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880452).length < 2 ^ (prefixWord ++ tailWord_2880452).sum := by decide
  have hdescent : baseEnd_2880452 < baseStart_2880452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880463 : List Nat := [1, 1, 2, 1, 1, 6, 1, 3, 6]
def baseStart_2880463 : Nat := 118140960795 + 2880463 * 2 ^ 59
def prefixEnd_2880463 : Nat := 4983230072969 + 3 ^ 40 * 2880463 * 2
def baseEnd_2880463 : Nat := 328680450331526424214555

theorem tailTrace_2880463 : CollatzResearch.WordTrace tailWord_2880463 prefixEnd_2880463 328680450331526424214555 := by
  unfold tailWord_2880463
  simp only [CollatzResearch.WordTrace]
  refine ⟨105059116563581969759854043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70039411042387979839902695 105059116563581969759854043)
  ·
    refine ⟨157588674845372954639781065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105059116563581969759854043 157588674845372954639781065)
    ·
      refine ⟨118191506134029715979835799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157588674845372954639781065 118191506134029715979835799)
      ·
        refine ⟨177287259201044573969753699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118191506134029715979835799 177287259201044573969753699)
        ·
          refine ⟨265930888801566860954630549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177287259201044573969753699 265930888801566860954630549)
          ·
            refine ⟨12465510412573446607248307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 265930888801566860954630549 12465510412573446607248307)
            ·
              refine ⟨18698265618860169910872461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12465510412573446607248307 18698265618860169910872461)
              ·
                refine ⟨7011849607072563716577173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18698265618860169910872461 7011849607072563716577173)
                ·
                  refine ⟨328680450331526424214555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7011849607072563716577173 328680450331526424214555)
                  ·
                    rfl

theorem cell22_2880463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 6].length) (baseStart_2880463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2880463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2880463 prefixEnd_2880463 := by exact prefixLift 2880463
  have htrace : WordTrace (prefixWord ++ tailWord_2880463) baseStart_2880463 baseEnd_2880463 := by
    simpa [prefixWord, tailWord_2880463, baseEnd_2880463] using wordTrace_append hprefix tailTrace_2880463
  have hstable : (prefixWord ++ tailWord_2880463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880463).length < 2 ^ (prefixWord ++ tailWord_2880463).sum := by decide
  have hdescent : baseEnd_2880463 < baseStart_2880463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880495 : List Nat := [1, 1, 2, 1, 4, 3, 1, 2, 4, 3]
def baseStart_2880495 : Nat := 118140960795 + 2880495 * 2 ^ 59
def prefixEnd_2880495 : Nat := 4983230072969 + 3 ^ 40 * 2880495 * 2
def baseEnd_2880495 : Nat := 986052305248541855843567

theorem tailTrace_2880495 : CollatzResearch.WordTrace tailWord_2880495 prefixEnd_2880495 986052305248541855843567 := by
  unfold tailWord_2880495
  simp only [CollatzResearch.WordTrace]
  refine ⟨105060283699466039225018939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70040189132977359483345959 105060283699466039225018939)
  ·
    refine ⟨157590425549199058837528409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105060283699466039225018939 157590425549199058837528409)
    ·
      refine ⟨118192819161899294128146307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157590425549199058837528409 118192819161899294128146307)
      ·
        refine ⟨177289228742848941192219461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118192819161899294128146307 177289228742848941192219461)
        ·
          refine ⟨33241730389284176473541149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 177289228742848941192219461 33241730389284176473541149)
          ·
            refine ⟨12465648895981566177577931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33241730389284176473541149 12465648895981566177577931)
            ·
              refine ⟨18698473343972349266366897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12465648895981566177577931 18698473343972349266366897)
              ·
                refine ⟨14023855007979261949775173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18698473343972349266366897 14023855007979261949775173)
                ·
                  refine ⟨2629472813996111615582845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14023855007979261949775173 2629472813996111615582845)
                  ·
                    refine ⟨986052305248541855843567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2629472813996111615582845 986052305248541855843567)
                    ·
                      rfl

theorem cell22_2880495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 4, 3].length) (baseStart_2880495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2880495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2880495 prefixEnd_2880495 := by exact prefixLift 2880495
  have htrace : WordTrace (prefixWord ++ tailWord_2880495) baseStart_2880495 baseEnd_2880495 := by
    simpa [prefixWord, tailWord_2880495, baseEnd_2880495] using wordTrace_append hprefix tailTrace_2880495
  have hstable : (prefixWord ++ tailWord_2880495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880495).length < 2 ^ (prefixWord ++ tailWord_2880495).sum := by decide
  have hdescent : baseEnd_2880495 < baseStart_2880495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880497 : List Nat := [1, 2, 2, 2, 4, 1, 3, 3, 4]
def baseStart_2880497 : Nat := 118140960795 + 2880497 * 2 ^ 59
def prefixEnd_2880497 : Nat := 4983230072969 + 3 ^ 40 * 2880497 * 2
def baseEnd_2880497 : Nat := 328684329963138172431187

theorem tailTrace_2880497 : CollatzResearch.WordTrace tailWord_2880497 prefixEnd_2880497 328684329963138172431187 := by
  unfold tailWord_2880497
  simp only [CollatzResearch.WordTrace]
  refine ⟨105060356645458793566591745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70040237763639195711061163 105060356645458793566591745)
  ·
    refine ⟨78795267484094095174943809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105060356645458793566591745 78795267484094095174943809)
    ·
      refine ⟨59096450613070571381207857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78795267484094095174943809 59096450613070571381207857)
      ·
        refine ⟨44322337959802928535905893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59096450613070571381207857 44322337959802928535905893)
        ·
          refine ⟨8310438367463049100482355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44322337959802928535905893 8310438367463049100482355)
          ·
            refine ⟨12465657551194573650723533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8310438367463049100482355 12465657551194573650723533)
            ·
              refine ⟨4674621581697965119021325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12465657551194573650723533 4674621581697965119021325)
              ·
                refine ⟨1752983093136736919632997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4674621581697965119021325 1752983093136736919632997)
                ·
                  refine ⟨328684329963138172431187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1752983093136736919632997 328684329963138172431187)
                  ·
                    rfl

theorem cell22_2880497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 3, 4].length) (baseStart_2880497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2880497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2880497 prefixEnd_2880497 := by exact prefixLift 2880497
  have htrace : WordTrace (prefixWord ++ tailWord_2880497) baseStart_2880497 baseEnd_2880497 := by
    simpa [prefixWord, tailWord_2880497, baseEnd_2880497] using wordTrace_append hprefix tailTrace_2880497
  have hstable : (prefixWord ++ tailWord_2880497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880497).length < 2 ^ (prefixWord ++ tailWord_2880497).sum := by decide
  have hdescent : baseEnd_2880497 < baseStart_2880497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880508 : List Nat := [2, 2, 2, 1, 2, 3, 10]
def baseStart_2880508 : Nat := 118140960795 + 2880508 * 2 ^ 59
def prefixEnd_2880508 : Nat := 4983230072969 + 3 ^ 40 * 2880508 * 2
def baseEnd_2880508 : Nat := 36520620570896820565501

theorem tailTrace_2880508 : CollatzResearch.WordTrace tailWord_2880508 prefixEnd_2880508 36520620570896820565501 := by
  unfold tailWord_2880508
  simp only [CollatzResearch.WordTrace]
  refine ⟨52530378924209471222621089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70040505232279294963494785 52530378924209471222621089)
  ·
    refine ⟨39397784193157103416965817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52530378924209471222621089 39397784193157103416965817)
    ·
      refine ⟨29548338144867827562724363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39397784193157103416965817 29548338144867827562724363)
      ·
        refine ⟨44322507217301741344086545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29548338144867827562724363 44322507217301741344086545)
        ·
          refine ⟨33241880412976306008064909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44322507217301741344086545 33241880412976306008064909)
          ·
            refine ⟨12465705154866114753024341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33241880412976306008064909 12465705154866114753024341)
            ·
              refine ⟨36520620570896820565501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12465705154866114753024341 36520620570896820565501)
              ·
                rfl

theorem cell22_2880508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 10].length) (baseStart_2880508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2880508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2880508 prefixEnd_2880508 := by exact prefixLift 2880508
  have htrace : WordTrace (prefixWord ++ tailWord_2880508) baseStart_2880508 baseEnd_2880508 := by
    simpa [prefixWord, tailWord_2880508, baseEnd_2880508] using wordTrace_append hprefix tailTrace_2880508
  have hstable : (prefixWord ++ tailWord_2880508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880508).length < 2 ^ (prefixWord ++ tailWord_2880508).sum := by decide
  have hdescent : baseEnd_2880508 < baseStart_2880508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880544 : List Nat := [2, 1, 1, 7, 1, 1, 2, 1, 2, 4]
def baseStart_2880544 : Nat := 118140960795 + 2880544 * 2 ^ 59
def prefixEnd_2880544 : Nat := 4983230072969 + 3 ^ 40 * 2880544 * 2
def baseEnd_2880544 : Nat := 986069078949922061368417

theorem tailTrace_2880544 : CollatzResearch.WordTrace tailWord_2880544 prefixEnd_2880544 986069078949922061368417 := by
  unfold tailWord_2880544
  simp only [CollatzResearch.WordTrace]
  refine ⟨52531035438144260296776343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70041380584192347062368457 52531035438144260296776343)
  ·
    refine ⟨78796553157216390445164515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52531035438144260296776343 78796553157216390445164515)
    ·
      refine ⟨118194829735824585667746773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78796553157216390445164515 118194829735824585667746773)
      ·
        refine ⟨2770191321933388726587815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 118194829735824585667746773 2770191321933388726587815)
        ·
          refine ⟨4155286982900083089881723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2770191321933388726587815 4155286982900083089881723)
          ·
            refine ⟨6232930474350124634822585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4155286982900083089881723 6232930474350124634822585)
            ·
              refine ⟨4674697855762593476116939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6232930474350124634822585 4674697855762593476116939)
              ·
                refine ⟨7012046783643890214175409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4674697855762593476116939 7012046783643890214175409)
                ·
                  refine ⟨5259035087732917660631557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7012046783643890214175409 5259035087732917660631557)
                  ·
                    refine ⟨986069078949922061368417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5259035087732917660631557 986069078949922061368417)
                    ·
                      rfl

theorem cell22_2880544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 2, 4].length) (baseStart_2880544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2880544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2880544 prefixEnd_2880544 := by exact prefixLift 2880544
  have htrace : WordTrace (prefixWord ++ tailWord_2880544) baseStart_2880544 baseEnd_2880544 := by
    simpa [prefixWord, tailWord_2880544, baseEnd_2880544] using wordTrace_append hprefix tailTrace_2880544
  have hstable : (prefixWord ++ tailWord_2880544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880544).length < 2 ^ (prefixWord ++ tailWord_2880544).sum := by decide
  have hdescent : baseEnd_2880544 < baseStart_2880544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880570 : List Nat := [3, 1, 1, 1, 3, 1, 3, 4, 5]
def baseStart_2880570 : Nat := 118140960795 + 2880570 * 2 ^ 59
def prefixEnd_2880570 : Nat := 4983230072969 + 3 ^ 40 * 2880570 * 2
def baseEnd_2880570 : Nat := 328692659760422220072779

theorem tailTrace_2880570 : CollatzResearch.WordTrace tailWord_2880570 prefixEnd_2880570 328692659760422220072779 := by
  unfold tailWord_2880570
  simp only [CollatzResearch.WordTrace]
  refine ⟨26265754793548581758499791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70042012782796218022666109 26265754793548581758499791)
  ·
    refine ⟨39398632190322872637749687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26265754793548581758499791 39398632190322872637749687)
    ·
      refine ⟨59097948285484308956624531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39398632190322872637749687 59097948285484308956624531)
      ·
        refine ⟨88646922428226463434936797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59097948285484308956624531 88646922428226463434936797)
        ·
          refine ⟨33242595910584923788101299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88646922428226463434936797 33242595910584923788101299)
          ·
            refine ⟨49863893865877385682151949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33242595910584923788101299 49863893865877385682151949)
            ·
              refine ⟨18698960199704019630806981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49863893865877385682151949 18698960199704019630806981)
              ·
                refine ⟨3506055037444503680776309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18698960199704019630806981 3506055037444503680776309)
                ·
                  refine ⟨328692659760422220072779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3506055037444503680776309 328692659760422220072779)
                  ·
                    rfl

theorem cell22_2880570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 4, 5].length) (baseStart_2880570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2880570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2880570 prefixEnd_2880570 := by exact prefixLift 2880570
  have htrace : WordTrace (prefixWord ++ tailWord_2880570) baseStart_2880570 baseEnd_2880570 := by
    simpa [prefixWord, tailWord_2880570, baseEnd_2880570] using wordTrace_append hprefix tailTrace_2880570
  have hstable : (prefixWord ++ tailWord_2880570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880570).length < 2 ^ (prefixWord ++ tailWord_2880570).sum := by decide
  have hdescent : baseEnd_2880570 < baseStart_2880570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880600 : List Nat := [2, 1, 2, 2, 1, 3, 1, 3, 3, 4]
def baseStart_2880600 : Nat := 118140960795 + 2880600 * 2 ^ 59
def prefixEnd_2880600 : Nat := 4983230072969 + 3 ^ 40 * 2880600 * 2
def baseEnd_2880600 : Nat := 986088248894356581968245

theorem tailTrace_2880600 : CollatzResearch.WordTrace tailWord_2880600 prefixEnd_2880600 986088248894356581968245 := by
  unfold tailWord_2880600
  simp only [CollatzResearch.WordTrace]
  refine ⟨52532056682042821078795627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70042742242723761438394169 52532056682042821078795627)
  ·
    refine ⟨78798085023064231618193441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52532056682042821078795627 78798085023064231618193441)
    ·
      refine ⟨59098563767298173713645081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78798085023064231618193441 59098563767298173713645081)
      ·
        refine ⟨44323922825473630285233811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59098563767298173713645081 44323922825473630285233811)
        ·
          refine ⟨66485884238210445427850717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44323922825473630285233811 66485884238210445427850717)
          ·
            refine ⟨24932206589328917035444019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66485884238210445427850717 24932206589328917035444019)
            ·
              refine ⟨37398309883993375553166029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24932206589328917035444019 37398309883993375553166029)
              ·
                refine ⟨14024366206497515832437261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37398309883993375553166029 14024366206497515832437261)
                ·
                  refine ⟨5259137327436568437163973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14024366206497515832437261 5259137327436568437163973)
                  ·
                    refine ⟨986088248894356581968245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5259137327436568437163973 986088248894356581968245)
                    ·
                      rfl

theorem cell22_2880600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 3, 4].length) (baseStart_2880600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2880600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2880600 prefixEnd_2880600 := by exact prefixLift 2880600
  have htrace : WordTrace (prefixWord ++ tailWord_2880600) baseStart_2880600 baseEnd_2880600 := by
    simpa [prefixWord, tailWord_2880600, baseEnd_2880600] using wordTrace_append hprefix tailTrace_2880600
  have hstable : (prefixWord ++ tailWord_2880600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880600).length < 2 ^ (prefixWord ++ tailWord_2880600).sum := by decide
  have hdescent : baseEnd_2880600 < baseStart_2880600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880617 : List Nat := [1, 2, 1, 1, 1, 7, 1, 3, 1, 4]
def baseStart_2880617 : Nat := 118140960795 + 2880617 * 2 ^ 59
def prefixEnd_2880617 : Nat := 4983230072969 + 3 ^ 40 * 2880617 * 2
def baseEnd_2880617 : Nat := 986094068341774204293193

theorem tailTrace_2880617 : CollatzResearch.WordTrace tailWord_2880617 prefixEnd_2880617 986094068341774204293193 := by
  unfold tailWord_2880617
  simp only [CollatzResearch.WordTrace]
  refine ⟨105064733405024054060960105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70043155603349369373973403 105064733405024054060960105)
  ·
    refine ⟨78798550053768040545720079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105064733405024054060960105 78798550053768040545720079)
    ·
      refine ⟨118197825080652060818580119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78798550053768040545720079 118197825080652060818580119)
      ·
        refine ⟨177296737620978091227870179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118197825080652060818580119 177296737620978091227870179)
        ·
          refine ⟨265945106431467136841805269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177296737620978091227870179 265945106431467136841805269)
          ·
            refine ⟨6233088431987511019729811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 265945106431467136841805269 6233088431987511019729811)
            ·
              refine ⟨9349632647981266529594717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6233088431987511019729811 9349632647981266529594717)
              ·
                refine ⟨3506112242992974948598019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9349632647981266529594717 3506112242992974948598019)
                ·
                  refine ⟨5259168364489462422897029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3506112242992974948598019 5259168364489462422897029)
                  ·
                    refine ⟨986094068341774204293193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5259168364489462422897029 986094068341774204293193)
                    ·
                      rfl

theorem cell22_2880617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 3, 1, 4].length) (baseStart_2880617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2880617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2880617 prefixEnd_2880617 := by exact prefixLift 2880617
  have htrace : WordTrace (prefixWord ++ tailWord_2880617) baseStart_2880617 baseEnd_2880617 := by
    simpa [prefixWord, tailWord_2880617, baseEnd_2880617] using wordTrace_append hprefix tailTrace_2880617
  have hstable : (prefixWord ++ tailWord_2880617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880617).length < 2 ^ (prefixWord ++ tailWord_2880617).sum := by decide
  have hdescent : baseEnd_2880617 < baseStart_2880617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880632 : List Nat := [2, 1, 2, 1, 1, 1, 6, 4, 4]
def baseStart_2880632 : Nat := 118140960795 + 2880632 * 2 ^ 59
def prefixEnd_2880632 : Nat := 4983230072969 + 3 ^ 40 * 2880632 * 2
def baseEnd_2880632 : Nat := 328699734382773055056049

theorem tailTrace_2880632 : CollatzResearch.WordTrace tailWord_2880632 prefixEnd_2880632 328699734382773055056049 := by
  unfold tailWord_2880632
  simp only [CollatzResearch.WordTrace]
  refine ⟨52532640249984855811378075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70043520333313141081837433 52532640249984855811378075)
  ·
    refine ⟨78798960374977283717067113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52532640249984855811378075 78798960374977283717067113)
    ·
      refine ⟨59099220281232962787800335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78798960374977283717067113 59099220281232962787800335)
      ·
        refine ⟨88648830421849444181700503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59099220281232962787800335 88648830421849444181700503)
        ·
          refine ⟨132973245632774166272550755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88648830421849444181700503 132973245632774166272550755)
          ·
            refine ⟨199459868449161249408826133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132973245632774166272550755 199459868449161249408826133)
            ·
              refine ⟨9349681333554433566038725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 199459868449161249408826133 9349681333554433566038725)
              ·
                refine ⟨1753065250041456293632261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9349681333554433566038725 1753065250041456293632261)
                ·
                  refine ⟨328699734382773055056049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1753065250041456293632261 328699734382773055056049)
                  ·
                    rfl

theorem cell22_2880632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 4, 4].length) (baseStart_2880632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2880632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2880632 prefixEnd_2880632 := by exact prefixLift 2880632
  have htrace : WordTrace (prefixWord ++ tailWord_2880632) baseStart_2880632 baseEnd_2880632 := by
    simpa [prefixWord, tailWord_2880632, baseEnd_2880632] using wordTrace_append hprefix tailTrace_2880632
  have hstable : (prefixWord ++ tailWord_2880632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880632).length < 2 ^ (prefixWord ++ tailWord_2880632).sum := by decide
  have hdescent : baseEnd_2880632 < baseStart_2880632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880666 : List Nat := [3, 1, 1, 5, 1, 3, 1, 3, 4]
def baseStart_2880666 : Nat := 118140960795 + 2880666 * 2 ^ 59
def prefixEnd_2880666 : Nat := 4983230072969 + 3 ^ 40 * 2880666 * 2
def baseEnd_2880666 : Nat := 328703614014384803272681

theorem tailTrace_2880666 : CollatzResearch.WordTrace tailWord_2880666 prefixEnd_2880666 328703614014384803272681 := by
  unfold tailWord_2880666
  simp only [CollatzResearch.WordTrace]
  refine ⟨26266630145461633857373463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70044347054564356952995901 26266630145461633857373463)
  ·
    refine ⟨39399945218192450786060195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26266630145461633857373463 39399945218192450786060195)
    ·
      refine ⟨59099917827288676179090293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39399945218192450786060195 59099917827288676179090293)
      ·
        refine ⟨5540617296308313391789715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59099917827288676179090293 5540617296308313391789715)
        ·
          refine ⟨8310925944462470087684573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5540617296308313391789715 8310925944462470087684573)
          ·
            refine ⟨3116597229173426282881715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8310925944462470087684573 3116597229173426282881715)
            ·
              refine ⟨4674895843760139424322573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3116597229173426282881715 4674895843760139424322573)
              ·
                refine ⟨1753085941410052284120965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4674895843760139424322573 1753085941410052284120965)
                ·
                  refine ⟨328703614014384803272681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1753085941410052284120965 328703614014384803272681)
                  ·
                    rfl

theorem cell22_2880666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 3, 4].length) (baseStart_2880666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2880666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2880666 prefixEnd_2880666 := by exact prefixLift 2880666
  have htrace : WordTrace (prefixWord ++ tailWord_2880666) baseStart_2880666 baseEnd_2880666 := by
    simpa [prefixWord, tailWord_2880666, baseEnd_2880666] using wordTrace_append hprefix tailTrace_2880666
  have hstable : (prefixWord ++ tailWord_2880666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880666).length < 2 ^ (prefixWord ++ tailWord_2880666).sum := by decide
  have hdescent : baseEnd_2880666 < baseStart_2880666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880679 : List Nat := [1, 1, 6, 2, 1, 2, 1, 2, 2, 4]
def baseStart_2880679 : Nat := 118140960795 + 2880679 * 2 ^ 59
def prefixEnd_2880679 : Nat := 4983230072969 + 3 ^ 40 * 2880679 * 2
def baseEnd_2880679 : Nat := 986115292208826709243003

theorem tailTrace_2880679 : CollatzResearch.WordTrace tailWord_2880679 prefixEnd_2880679 986115292208826709243003 := by
  unfold tailWord_2880679
  simp only [CollatzResearch.WordTrace]
  refine ⟨105066994730799438649717091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70044663153866292433144727 105066994730799438649717091)
  ·
    refine ⟨157600492096199157974575637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105066994730799438649717091 157600492096199157974575637)
    ·
      refine ⟨7387523067009335530058233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 157600492096199157974575637 7387523067009335530058233)
      ·
        refine ⟨5540642300257001647543675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7387523067009335530058233 5540642300257001647543675)
        ·
          refine ⟨8310963450385502471315513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5540642300257001647543675 8310963450385502471315513)
          ·
            refine ⟨6233222587789126853486635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8310963450385502471315513 6233222587789126853486635)
            ·
              refine ⟨9349833881683690280229953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6233222587789126853486635 9349833881683690280229953)
              ·
                refine ⟨7012375411262767710172465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9349833881683690280229953 7012375411262767710172465)
                ·
                  refine ⟨5259281558447075782629349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7012375411262767710172465 5259281558447075782629349)
                  ·
                    refine ⟨986115292208826709243003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5259281558447075782629349 986115292208826709243003)
                    ·
                      rfl

theorem cell22_2880679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_2880679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2880679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2880679 prefixEnd_2880679 := by exact prefixLift 2880679
  have htrace : WordTrace (prefixWord ++ tailWord_2880679) baseStart_2880679 baseEnd_2880679 := by
    simpa [prefixWord, tailWord_2880679, baseEnd_2880679] using wordTrace_append hprefix tailTrace_2880679
  have hstable : (prefixWord ++ tailWord_2880679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880679).length < 2 ^ (prefixWord ++ tailWord_2880679).sum := by decide
  have hdescent : baseEnd_2880679 < baseStart_2880679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880743 : List Nat := [1, 1, 5, 3, 2, 1, 1, 4, 1, 3]
def baseStart_2880743 : Nat := 118140960795 + 2880743 * 2 ^ 59
def prefixEnd_2880743 : Nat := 4983230072969 + 3 ^ 40 * 2880743 * 2
def baseEnd_2880743 : Nat := 986137200716751875642807

theorem tailTrace_2880743 : CollatzResearch.WordTrace tailWord_2880743 prefixEnd_2880743 986137200716751875642807 := by
  unfold tailWord_2880743
  simp only [CollatzResearch.WordTrace]
  refine ⟨105069329002567577580046883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70046219335045051720031255 105069329002567577580046883)
  ·
    refine ⟨157603993503851366370070325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105069329002567577580046883 157603993503851366370070325)
    ·
      refine ⟨14775374390986065597194093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 157603993503851366370070325 14775374390986065597194093)
      ·
        refine ⟨5540765396619774598947785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14775374390986065597194093 5540765396619774598947785)
        ·
          refine ⟨4155574047464830949210839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5540765396619774598947785 4155574047464830949210839)
          ·
            refine ⟨6233361071197246423816259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4155574047464830949210839 6233361071197246423816259)
            ·
              refine ⟨9350041606795869635724389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6233361071197246423816259 9350041606795869635724389)
              ·
                refine ⟨1753132801274225556698323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9350041606795869635724389 1753132801274225556698323)
                ·
                  refine ⟨2629699201911338335047485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1753132801274225556698323 2629699201911338335047485)
                  ·
                    refine ⟨986137200716751875642807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2629699201911338335047485 986137200716751875642807)
                    ·
                      rfl

theorem cell22_2880743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_2880743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2880743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2880743 prefixEnd_2880743 := by exact prefixLift 2880743
  have htrace : WordTrace (prefixWord ++ tailWord_2880743) baseStart_2880743 baseEnd_2880743 := by
    simpa [prefixWord, tailWord_2880743, baseEnd_2880743] using wordTrace_append hprefix tailTrace_2880743
  have hstable : (prefixWord ++ tailWord_2880743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880743).length < 2 ^ (prefixWord ++ tailWord_2880743).sum := by decide
  have hdescent : baseEnd_2880743 < baseStart_2880743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880754 : List Nat := [3, 2, 1, 3, 3, 1, 1, 1, 2, 5]
def baseStart_2880754 : Nat := 118140960795 + 2880754 * 2 ^ 59
def prefixEnd_2880754 : Nat := 4983230072969 + 3 ^ 40 * 2880754 * 2
def baseEnd_2880754 : Nat := 986140966241551513617773

theorem tailTrace_2880754 : CollatzResearch.WordTrace tailWord_2880754 prefixEnd_2880754 986140966241551513617773 := by
  unfold tailWord_2880754
  simp only [CollatzResearch.WordTrace]
  refine ⟨26267432551381931614674329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70046486803685150972464877 26267432551381931614674329)
  ·
    refine ⟨19700574413536448711005747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26267432551381931614674329 19700574413536448711005747)
    ·
      refine ⟨29550861620304673066508621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19700574413536448711005747 29550861620304673066508621)
      ·
        refine ⟨11081573107614252399940733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29550861620304673066508621 11081573107614252399940733)
        ·
          refine ⟨4155589915355344649977775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11081573107614252399940733 4155589915355344649977775)
          ·
            refine ⟨6233384873033016974966663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4155589915355344649977775 6233384873033016974966663)
            ·
              refine ⟨9350077309549525462449995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6233384873033016974966663 9350077309549525462449995)
              ·
                refine ⟨14025115964324288193674993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9350077309549525462449995 14025115964324288193674993)
                ·
                  refine ⟨10518836973243216145256245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14025115964324288193674993 10518836973243216145256245)
                  ·
                    refine ⟨986140966241551513617773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10518836973243216145256245 986140966241551513617773)
                    ·
                      rfl

theorem cell22_2880754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_2880754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2880754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2880754 prefixEnd_2880754 := by exact prefixLift 2880754
  have htrace : WordTrace (prefixWord ++ tailWord_2880754) baseStart_2880754 baseEnd_2880754 := by
    simpa [prefixWord, tailWord_2880754, baseEnd_2880754] using wordTrace_append hprefix tailTrace_2880754
  have hstable : (prefixWord ++ tailWord_2880754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880754).length < 2 ^ (prefixWord ++ tailWord_2880754).sum := by decide
  have hdescent : baseEnd_2880754 < baseStart_2880754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880767 : List Nat := [1, 1, 2, 2, 1, 6, 1, 2, 6]
def baseStart_2880767 : Nat := 118140960795 + 2880767 * 2 ^ 59
def prefixEnd_2880767 : Nat := 4983230072969 + 3 ^ 40 * 2880767 * 2
def baseEnd_2880767 : Nat := 328715138802407937680911

theorem tailTrace_2880767 : CollatzResearch.WordTrace tailWord_2880767 prefixEnd_2880767 328715138802407937680911 := by
  unfold tailWord_2880767
  simp only [CollatzResearch.WordTrace]
  refine ⟨105070204354480629678920555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70046802902987086452613703 105070204354480629678920555)
  ·
    refine ⟨157605306531720944518380833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105070204354480629678920555 157605306531720944518380833)
    ·
      refine ⟨118203979898790708388785625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157605306531720944518380833 118203979898790708388785625)
      ·
        refine ⟨88652984924093031291589219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118203979898790708388785625 88652984924093031291589219)
        ·
          refine ⟨132979477386139546937383829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88652984924093031291589219 132979477386139546937383829)
          ·
            refine ⟨6233413002475291262689867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 132979477386139546937383829 6233413002475291262689867)
            ·
              refine ⟨9350119503712936894034801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6233413002475291262689867 9350119503712936894034801)
              ·
                refine ⟨7012589627784702670526101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9350119503712936894034801 7012589627784702670526101)
                ·
                  refine ⟨328715138802407937680911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7012589627784702670526101 328715138802407937680911)
                  ·
                    rfl

theorem cell22_2880767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 6].length) (baseStart_2880767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2880767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2880767 prefixEnd_2880767 := by exact prefixLift 2880767
  have htrace : WordTrace (prefixWord ++ tailWord_2880767) baseStart_2880767 baseEnd_2880767 := by
    simpa [prefixWord, tailWord_2880767, baseEnd_2880767] using wordTrace_append hprefix tailTrace_2880767
  have hstable : (prefixWord ++ tailWord_2880767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880767).length < 2 ^ (prefixWord ++ tailWord_2880767).sum := by decide
  have hdescent : baseEnd_2880767 < baseStart_2880767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880816 : List Nat := [2, 1, 1, 1, 2, 2, 7, 1, 2, 3]
def baseStart_2880816 : Nat := 118140960795 + 2880816 * 2 ^ 59
def prefixEnd_2880816 : Nat := 4983230072969 + 3 ^ 40 * 2880816 * 2
def baseEnd_2880816 : Nat := 986162190108604018567583

theorem tailTrace_2880816 : CollatzResearch.WordTrace tailWord_2880816 prefixEnd_2880816 986162190108604018567583 := by
  unfold tailWord_2880816
  simp only [CollatzResearch.WordTrace]
  refine ⟨52535995765651555523727151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70047994354202074031636201 52535995765651555523727151)
  ·
    refine ⟨78803993648477333285590727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52535995765651555523727151 78803993648477333285590727)
    ·
      refine ⟨118205990472715999928386091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78803993648477333285590727 118205990472715999928386091)
      ·
        refine ⟨177308985709073999892579137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118205990472715999928386091 177308985709073999892579137)
        ·
          refine ⟨132981739281805499919434353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177308985709073999892579137 132981739281805499919434353)
          ·
            refine ⟨99736304461354124939575765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132981739281805499919434353 99736304461354124939575765)
            ·
              refine ⟨2337569635812987303271307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 99736304461354124939575765 2337569635812987303271307)
              ·
                refine ⟨3506354453719480954906961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2337569635812987303271307 3506354453719480954906961)
                ·
                  refine ⟨2629765840289610716180221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3506354453719480954906961 2629765840289610716180221)
                  ·
                    refine ⟨986162190108604018567583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2629765840289610716180221 986162190108604018567583)
                    ·
                      rfl

theorem cell22_2880816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 1, 2, 3].length) (baseStart_2880816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2880816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2880816 prefixEnd_2880816 := by exact prefixLift 2880816
  have htrace : WordTrace (prefixWord ++ tailWord_2880816) baseStart_2880816 baseEnd_2880816 := by
    simpa [prefixWord, tailWord_2880816, baseEnd_2880816] using wordTrace_append hprefix tailTrace_2880816
  have hstable : (prefixWord ++ tailWord_2880816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880816).length < 2 ^ (prefixWord ++ tailWord_2880816).sum := by decide
  have hdescent : baseEnd_2880816 < baseStart_2880816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880857 : List Nat := [1, 2, 1, 2, 2, 2, 4, 1, 7]
def baseStart_2880857 : Nat := 118140960795 + 2880857 * 2 ^ 59
def prefixEnd_2880857 : Nat := 4983230072969 + 3 ^ 40 * 2880857 * 2
def baseEnd_2880857 : Nat := 328725408415497859430819

theorem tailTrace_2880857 : CollatzResearch.WordTrace tailWord_2880857 prefixEnd_2880857 328725408415497859430819 := by
  unfold tailWord_2880857
  simp only [CollatzResearch.WordTrace]
  refine ⟨105073486924154575049696825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70048991282769716699797883 105073486924154575049696825)
  ·
    refine ⟨78805115193115931287272619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105073486924154575049696825 78805115193115931287272619)
    ·
      refine ⟨118207672789673896930908929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78805115193115931287272619 118207672789673896930908929)
      ·
        refine ⟨88655754592255422698181697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118207672789673896930908929 88655754592255422698181697)
        ·
          refine ⟨66491815944191567023636273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88655754592255422698181697 66491815944191567023636273)
          ·
            refine ⟨49868861958143675267727205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66491815944191567023636273 49868861958143675267727205)
            ·
              refine ⟨9350411617151939112698851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49868861958143675267727205 9350411617151939112698851)
              ·
                refine ⟨14025617425727908669048277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9350411617151939112698851 14025617425727908669048277)
                ·
                  refine ⟨328725408415497859430819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14025617425727908669048277 328725408415497859430819)
                  ·
                    rfl

theorem cell22_2880857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 7].length) (baseStart_2880857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2880857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2880857 prefixEnd_2880857 := by exact prefixLift 2880857
  have htrace : WordTrace (prefixWord ++ tailWord_2880857) baseStart_2880857 baseEnd_2880857 := by
    simpa [prefixWord, tailWord_2880857, baseEnd_2880857] using wordTrace_append hprefix tailTrace_2880857
  have hstable : (prefixWord ++ tailWord_2880857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880857).length < 2 ^ (prefixWord ++ tailWord_2880857).sum := by decide
  have hdescent : baseEnd_2880857 < baseStart_2880857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880947 : List Nat := [1, 1, 1, 2, 3, 1, 1, 12]
def baseStart_2880947 : Nat := 118140960795 + 2880947 * 2 ^ 59
def prefixEnd_2880947 : Nat := 4983230072969 + 3 ^ 40 * 2880947 * 2
def baseEnd_2880947 : Nat := 109578559342862593726909

theorem tailTrace_2880947 : CollatzResearch.WordTrace tailWord_2880947 prefixEnd_2880947 109578559342862593726909 := by
  unfold tailWord_2880947
  simp only [CollatzResearch.WordTrace]
  refine ⟨105076769493828520420473095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70051179662552346946982063 105076769493828520420473095)
  ·
    refine ⟨157615154240742780630709643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105076769493828520420473095 157615154240742780630709643)
    ·
      refine ⟨236422731361114170946064465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157615154240742780630709643 236422731361114170946064465)
      ·
        refine ⟨177317048520835628209548349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236422731361114170946064465 177317048520835628209548349)
        ·
          refine ⟨66493893195313360578580631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177317048520835628209548349 66493893195313360578580631)
          ·
            refine ⟨99740839792970040867870947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66493893195313360578580631 99740839792970040867870947)
            ·
              refine ⟨149611259689455061301806421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99740839792970040867870947 149611259689455061301806421)
              ·
                refine ⟨109578559342862593726909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 149611259689455061301806421 109578559342862593726909)
                ·
                  rfl

theorem cell22_2880947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 12].length) (baseStart_2880947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2880947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2880947 prefixEnd_2880947 := by exact prefixLift 2880947
  have htrace : WordTrace (prefixWord ++ tailWord_2880947) baseStart_2880947 baseEnd_2880947 := by
    simpa [prefixWord, tailWord_2880947, baseEnd_2880947] using wordTrace_append hprefix tailTrace_2880947
  have hstable : (prefixWord ++ tailWord_2880947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880947).length < 2 ^ (prefixWord ++ tailWord_2880947).sum := by decide
  have hdescent : baseEnd_2880947 < baseStart_2880947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2880953 : List Nat := [1, 2, 1, 4, 4, 1, 2, 3, 4]
def baseStart_2880953 : Nat := 118140960795 + 2880953 * 2 ^ 59
def prefixEnd_2880953 : Nat := 4983230072969 + 3 ^ 40 * 2880953 * 2
def baseEnd_2880953 : Nat := 328736362669460442630721

theorem tailTrace_2880953 : CollatzResearch.WordTrace tailWord_2880953 prefixEnd_2880953 328736362669460442630721 := by
  unfold tailWord_2880953
  simp only [CollatzResearch.WordTrace]
  refine ⟨105076988331806783445191513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70051325554537855630127675 105076988331806783445191513)
  ·
    refine ⟨78807741248855087583893635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105076988331806783445191513 78807741248855087583893635)
    ·
      refine ⟨118211611873282631375840453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78807741248855087583893635 118211611873282631375840453)
      ·
        refine ⟨22164677226240493382970085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118211611873282631375840453 22164677226240493382970085)
        ·
          refine ⟨4155876979920092509306891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22164677226240493382970085 4155876979920092509306891)
          ·
            refine ⟨6233815469880138763960337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4155876979920092509306891 6233815469880138763960337)
            ·
              refine ⟨4675361602410104072970253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6233815469880138763960337 4675361602410104072970253)
              ·
                refine ⟨1753260600903789027363845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4675361602410104072970253 1753260600903789027363845)
                ·
                  refine ⟨328736362669460442630721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1753260600903789027363845 328736362669460442630721)
                  ·
                    rfl

theorem cell22_2880953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 3, 4].length) (baseStart_2880953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2880953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2880953 prefixEnd_2880953 := by exact prefixLift 2880953
  have htrace : WordTrace (prefixWord ++ tailWord_2880953) baseStart_2880953 baseEnd_2880953 := by
    simpa [prefixWord, tailWord_2880953, baseEnd_2880953] using wordTrace_append hprefix tailTrace_2880953
  have hstable : (prefixWord ++ tailWord_2880953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2880953).length < 2 ^ (prefixWord ++ tailWord_2880953).sum := by decide
  have hdescent : baseEnd_2880953 < baseStart_2880953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2880953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881009 : List Nat := [1, 2, 2, 2, 3, 2, 1, 2, 7]
def baseStart_2881009 : Nat := 118140960795 + 2881009 * 2 ^ 59
def prefixEnd_2881009 : Nat := 4983230072969 + 3 ^ 40 * 2881009 * 2
def baseEnd_2881009 : Nat := 328742752650938616163997

theorem tailTrace_2881009 : CollatzResearch.WordTrace tailWord_2881009 prefixEnd_2881009 328742752650938616163997 := by
  unfold tailWord_2881009
  simp only [CollatzResearch.WordTrace]
  refine ⟨105079030819603905009230081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70052687213069270006153387 105079030819603905009230081)
  ·
    refine ⟨78809273114702928756922561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105079030819603905009230081 78809273114702928756922561)
    ·
      refine ⟨59106954836027196567691921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78809273114702928756922561 59106954836027196567691921)
      ·
        refine ⟨44330216127020397425768941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59106954836027196567691921 44330216127020397425768941)
        ·
          refine ⟨16623831047632649034663353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44330216127020397425768941 16623831047632649034663353)
          ·
            refine ⟨12467873285724486775997515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16623831047632649034663353 12467873285724486775997515)
            ·
              refine ⟨18701809928586730163996273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12467873285724486775997515 18701809928586730163996273)
              ·
                refine ⟨14026357446440047622997205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18701809928586730163996273 14026357446440047622997205)
                ·
                  refine ⟨328742752650938616163997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14026357446440047622997205 328742752650938616163997)
                  ·
                    rfl

theorem cell22_2881009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 7].length) (baseStart_2881009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2881009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2881009 prefixEnd_2881009 := by exact prefixLift 2881009
  have htrace : WordTrace (prefixWord ++ tailWord_2881009) baseStart_2881009 baseEnd_2881009 := by
    simpa [prefixWord, tailWord_2881009, baseEnd_2881009] using wordTrace_append hprefix tailTrace_2881009
  have hstable : (prefixWord ++ tailWord_2881009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881009).length < 2 ^ (prefixWord ++ tailWord_2881009).sum := by decide
  have hdescent : baseEnd_2881009 < baseStart_2881009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881043 : List Nat := [1, 1, 1, 2, 1, 8, 2, 1, 5]
def baseStart_2881043 : Nat := 118140960795 + 2881043 * 2 ^ 59
def prefixEnd_2881043 : Nat := 4983230072969 + 3 ^ 40 * 2881043 * 2
def baseEnd_2881043 : Nat := 328746632282550364380629

theorem tailTrace_2881043 : CollatzResearch.WordTrace tailWord_2881043 prefixEnd_2881043 328746632282550364380629 := by
  unfold tailWord_2881043
  simp only [CollatzResearch.WordTrace]
  refine ⟨105080270901480728815967783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70053513934320485877311855 105080270901480728815967783)
  ·
    refine ⟨157620406352221093223951675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105080270901480728815967783 157620406352221093223951675)
    ·
      refine ⟨236430609528331639835927513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157620406352221093223951675 236430609528331639835927513)
      ·
        refine ⟨177322957146248729876945635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236430609528331639835927513 177322957146248729876945635)
        ·
          refine ⟨265984435719373094815418453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177322957146248729876945635 265984435719373094815418453)
          ·
            refine ⟨3117005106086403454868185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 265984435719373094815418453 3117005106086403454868185)
            ·
              refine ⟨2337753829564802591151139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3117005106086403454868185 2337753829564802591151139)
              ·
                refine ⟨3506630744347203886726709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2337753829564802591151139 3506630744347203886726709)
                ·
                  refine ⟨328746632282550364380629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3506630744347203886726709 328746632282550364380629)
                  ·
                    rfl

theorem cell22_2881043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 1, 5].length) (baseStart_2881043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2881043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2881043 prefixEnd_2881043 := by exact prefixLift 2881043
  have htrace : WordTrace (prefixWord ++ tailWord_2881043) baseStart_2881043 baseEnd_2881043 := by
    simpa [prefixWord, tailWord_2881043, baseEnd_2881043] using wordTrace_append hprefix tailTrace_2881043
  have hstable : (prefixWord ++ tailWord_2881043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881043).length < 2 ^ (prefixWord ++ tailWord_2881043).sum := by decide
  have hdescent : baseEnd_2881043 < baseStart_2881043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881161 : List Nat := [1, 2, 1, 1, 4, 1, 2, 5, 5]
def baseStart_2881161 : Nat := 118140960795 + 2881161 * 2 ^ 59
def prefixEnd_2881161 : Nat := 4983230072969 + 3 ^ 40 * 2881161 * 2
def baseEnd_2881161 : Nat := 328760096886379372897175

theorem tailTrace_2881161 : CollatzResearch.WordTrace tailWord_2881161 prefixEnd_2881161 328760096886379372897175 := by
  unfold tailWord_2881161
  simp only [CollatzResearch.WordTrace]
  refine ⟨105084574715053234968763337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70056383143368823312508891 105084574715053234968763337)
  ·
    refine ⟨78813431036289926226572503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105084574715053234968763337 78813431036289926226572503)
    ·
      refine ⟨118220146554434889339858755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78813431036289926226572503 118220146554434889339858755)
      ·
        refine ⟨177330219831652334009788133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118220146554434889339858755 177330219831652334009788133)
        ·
          refine ⟨33249416218434812626835275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 177330219831652334009788133 33249416218434812626835275)
          ·
            refine ⟨49874124327652218940252913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33249416218434812626835275 49874124327652218940252913)
            ·
              refine ⟨37405593245739164205189685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49874124327652218940252913 37405593245739164205189685)
              ·
                refine ⟨3506774366788046644236533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37405593245739164205189685 3506774366788046644236533)
                ·
                  refine ⟨328760096886379372897175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3506774366788046644236533 328760096886379372897175)
                  ·
                    rfl

theorem cell22_2881161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 5, 5].length) (baseStart_2881161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2881161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2881161 prefixEnd_2881161 := by exact prefixLift 2881161
  have htrace : WordTrace (prefixWord ++ tailWord_2881161) baseStart_2881161 baseEnd_2881161 := by
    simpa [prefixWord, tailWord_2881161, baseEnd_2881161] using wordTrace_append hprefix tailTrace_2881161
  have hstable : (prefixWord ++ tailWord_2881161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881161).length < 2 ^ (prefixWord ++ tailWord_2881161).sum := by decide
  have hdescent : baseEnd_2881161 < baseStart_2881161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881251 : List Nat := [1, 1, 1, 7, 12]
def baseStart_2881251 : Nat := 118140960795 + 2881251 * 2 ^ 59
def prefixEnd_2881251 : Nat := 4983230072969 + 3 ^ 40 * 2881251 * 2
def baseEnd_2881251 : Nat := 4058893413573694995643

theorem tailTrace_2881251 : CollatzResearch.WordTrace tailWord_2881251 prefixEnd_2881251 4058893413573694995643 := by
  unfold tailWord_2881251
  simp only [CollatzResearch.WordTrace]
  refine ⟨105087857284727180339539607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70058571523151453559693071 105087857284727180339539607)
  ·
    refine ⟨157631785927090770509309411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105087857284727180339539607 157631785927090770509309411)
    ·
      refine ⟨236447678890636155763964117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157631785927090770509309411 236447678890636155763964117)
      ·
        refine ⟨5541742473999284900717909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 236447678890636155763964117 5541742473999284900717909)
        ·
          refine ⟨4058893413573694995643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 5541742473999284900717909 4058893413573694995643)
          ·
            rfl

theorem cell22_2881251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 12].length) (baseStart_2881251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2881251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2881251 prefixEnd_2881251 := by exact prefixLift 2881251
  have htrace : WordTrace (prefixWord ++ tailWord_2881251) baseStart_2881251 baseEnd_2881251 := by
    simpa [prefixWord, tailWord_2881251, baseEnd_2881251] using wordTrace_append hprefix tailTrace_2881251
  have hstable : (prefixWord ++ tailWord_2881251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881251).length < 2 ^ (prefixWord ++ tailWord_2881251).sum := by decide
  have hdescent : baseEnd_2881251 < baseStart_2881251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881253 : List Nat := [1, 3, 1, 4, 1, 1, 1, 4, 2, 4]
def baseStart_2881253 : Nat := 118140960795 + 2881253 * 2 ^ 59
def prefixEnd_2881253 : Nat := 4983230072969 + 3 ^ 40 * 2881253 * 2
def baseEnd_2881253 : Nat := 986311784139280545391243

theorem tailTrace_2881253 : CollatzResearch.WordTrace tailWord_2881253 prefixEnd_2881253 986311784139280545391243 := by
  unfold tailWord_2881253
  simp only [CollatzResearch.WordTrace]
  refine ⟨105087930230719934681112413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70058620153813289787408275 105087930230719934681112413)
  ·
    refine ⟨39407973836519975505417155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105087930230719934681112413 39407973836519975505417155)
    ·
      refine ⟨59111960754779963258125733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39407973836519975505417155 59111960754779963258125733)
      ·
        refine ⟨11083492641521243110898575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59111960754779963258125733 11083492641521243110898575)
        ·
          refine ⟨16625238962281864666347863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11083492641521243110898575 16625238962281864666347863)
          ·
            refine ⟨24937858443422796999521795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16625238962281864666347863 24937858443422796999521795)
            ·
              refine ⟨37406787665134195499282693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24937858443422796999521795 37406787665134195499282693)
              ·
                refine ⟨7013772687212661656115505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37406787665134195499282693 7013772687212661656115505)
                ·
                  refine ⟨5260329515409496242086629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7013772687212661656115505 5260329515409496242086629)
                  ·
                    refine ⟨986311784139280545391243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5260329515409496242086629 986311784139280545391243)
                    ·
                      rfl

theorem cell22_2881253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 2, 4].length) (baseStart_2881253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2881253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2881253 prefixEnd_2881253 := by exact prefixLift 2881253
  have htrace : WordTrace (prefixWord ++ tailWord_2881253) baseStart_2881253 baseEnd_2881253 := by
    simpa [prefixWord, tailWord_2881253, baseEnd_2881253] using wordTrace_append hprefix tailTrace_2881253
  have hstable : (prefixWord ++ tailWord_2881253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881253).length < 2 ^ (prefixWord ++ tailWord_2881253).sum := by decide
  have hdescent : baseEnd_2881253 < baseStart_2881253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881283 : List Nat := [1, 1, 1, 3, 2, 2, 3, 1, 5, 3]
def baseStart_2881283 : Nat := 118140960795 + 2881283 * 2 ^ 59
def prefixEnd_2881283 : Nat := 4983230072969 + 3 ^ 40 * 2881283 * 2
def baseEnd_2881283 : Nat := 986322053752370467141151

theorem tailTrace_2881283 : CollatzResearch.WordTrace tailWord_2881283 prefixEnd_2881283 986322053752370467141151 := by
  unfold tailWord_2881283
  simp only [CollatzResearch.WordTrace]
  refine ⟨105089024420611249804704503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70059349613740833203136335 105089024420611249804704503)
  ·
    refine ⟨157633536630916874707056755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105089024420611249804704503 157633536630916874707056755)
    ·
      refine ⟨236450304946375312060585133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157633536630916874707056755 236450304946375312060585133)
      ·
        refine ⟨88668864354890742022719425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236450304946375312060585133 88668864354890742022719425)
        ·
          refine ⟨66501648266168056517039569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88668864354890742022719425 66501648266168056517039569)
          ·
            refine ⟨49876236199626042387779677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66501648266168056517039569 49876236199626042387779677)
            ·
              refine ⟨18703588574859765895417379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49876236199626042387779677 18703588574859765895417379)
              ·
                refine ⟨28055382862289648843126069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18703588574859765895417379 28055382862289648843126069)
                ·
                  refine ⟨2630192143339654579043069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28055382862289648843126069 2630192143339654579043069)
                  ·
                    refine ⟨986322053752370467141151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2630192143339654579043069 986322053752370467141151)
                    ·
                      rfl

theorem cell22_2881283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 5, 3].length) (baseStart_2881283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2881283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2881283 prefixEnd_2881283 := by exact prefixLift 2881283
  have htrace : WordTrace (prefixWord ++ tailWord_2881283) baseStart_2881283 baseEnd_2881283 := by
    simpa [prefixWord, tailWord_2881283, baseEnd_2881283] using wordTrace_append hprefix tailTrace_2881283
  have hstable : (prefixWord ++ tailWord_2881283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881283).length < 2 ^ (prefixWord ++ tailWord_2881283).sum := by decide
  have hdescent : baseEnd_2881283 < baseStart_2881283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881287 : List Nat := [1, 1, 4, 4, 2, 2, 1, 1, 2, 4]
def baseStart_2881287 : Nat := 118140960795 + 2881287 * 2 ^ 59
def prefixEnd_2881287 : Nat := 4983230072969 + 3 ^ 40 * 2881287 * 2
def baseEnd_2881287 : Nat := 986323423034115790041139

theorem tailTrace_2881287 : CollatzResearch.WordTrace tailWord_2881287 prefixEnd_2881287 986323423034115790041139 := by
  unfold tailWord_2881287
  simp only [CollatzResearch.WordTrace]
  refine ⟨105089170312596758487850115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70059446875064505658566743 105089170312596758487850115)
  ·
    refine ⟨157633755468895137731775173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105089170312596758487850115 157633755468895137731775173)
    ·
      refine ⟨29556329150417838324707845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157633755468895137731775173 29556329150417838324707845)
      ·
        refine ⟨5541811715703344685882721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29556329150417838324707845 5541811715703344685882721)
        ·
          refine ⟨4156358786777508514412041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5541811715703344685882721 4156358786777508514412041)
          ·
            refine ⟨3117269090083131385809031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4156358786777508514412041 3117269090083131385809031)
            ·
              refine ⟨4675903635124697078713547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3117269090083131385809031 4675903635124697078713547)
              ·
                refine ⟨7013855452687045618070321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4675903635124697078713547 7013855452687045618070321)
                ·
                  refine ⟨5260391589515284213552741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7013855452687045618070321 5260391589515284213552741)
                  ·
                    refine ⟨986323423034115790041139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5260391589515284213552741 986323423034115790041139)
                    ·
                      rfl

theorem cell22_2881287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 2, 4].length) (baseStart_2881287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2881287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2881287 prefixEnd_2881287 := by exact prefixLift 2881287
  have htrace : WordTrace (prefixWord ++ tailWord_2881287) baseStart_2881287 baseEnd_2881287 := by
    simpa [prefixWord, tailWord_2881287, baseEnd_2881287] using wordTrace_append hprefix tailTrace_2881287
  have hstable : (prefixWord ++ tailWord_2881287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881287).length < 2 ^ (prefixWord ++ tailWord_2881287).sum := by decide
  have hdescent : baseEnd_2881287 < baseStart_2881287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881313 : List Nat := [1, 2, 3, 2, 1, 4, 1, 1, 7]
def baseStart_2881313 : Nat := 118140960795 + 2881313 * 2 ^ 59
def prefixEnd_2881313 : Nat := 4983230072969 + 3 ^ 40 * 2881313 * 2
def baseEnd_2881313 : Nat := 328777441121820129630353

theorem tailTrace_2881313 : CollatzResearch.WordTrace tailWord_2881313 prefixEnd_2881313 328777441121820129630353 := by
  unfold tailWord_2881313
  simp only [CollatzResearch.WordTrace]
  refine ⟨105090118610502564928296593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70060079073668376618864395 105090118610502564928296593)
  ·
    refine ⟨78817588957876923696222445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105090118610502564928296593 78817588957876923696222445)
    ·
      refine ⟨29556595859203846386083417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78817588957876923696222445 29556595859203846386083417)
      ·
        refine ⟨22167446894402884789562563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29556595859203846386083417 22167446894402884789562563)
        ·
          refine ⟨33251170341604327184343845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22167446894402884789562563 33251170341604327184343845)
          ·
            refine ⟨6234594439050811347064471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33251170341604327184343845 6234594439050811347064471)
            ·
              refine ⟨9351891658576217020596707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6234594439050811347064471 9351891658576217020596707)
              ·
                refine ⟨14027837487864325530895061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9351891658576217020596707 14027837487864325530895061)
                ·
                  refine ⟨328777441121820129630353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14027837487864325530895061 328777441121820129630353)
                  ·
                    rfl

theorem cell22_2881313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 7].length) (baseStart_2881313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2881313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2881313 prefixEnd_2881313 := by exact prefixLift 2881313
  have htrace : WordTrace (prefixWord ++ tailWord_2881313) baseStart_2881313 baseEnd_2881313 := by
    simpa [prefixWord, tailWord_2881313, baseEnd_2881313] using wordTrace_append hprefix tailTrace_2881313
  have hstable : (prefixWord ++ tailWord_2881313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881313).length < 2 ^ (prefixWord ++ tailWord_2881313).sum := by decide
  have hdescent : baseEnd_2881313 < baseStart_2881313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881317 : List Nat := [1, 3, 1, 2, 3, 2, 2, 4, 1, 3]
def baseStart_2881317 : Nat := 118140960795 + 2881317 * 2 ^ 59
def prefixEnd_2881317 : Nat := 4983230072969 + 3 ^ 40 * 2881317 * 2
def baseEnd_2881317 : Nat := 986333692647205711791047

theorem tailTrace_2881317 : CollatzResearch.WordTrace tailWord_2881317 prefixEnd_2881317 986333692647205711791047 := by
  unfold tailWord_2881317
  simp only [CollatzResearch.WordTrace]
  refine ⟨105090264502488073611442205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70060176334992049074294803 105090264502488073611442205)
  ·
    refine ⟨39408849188433027604290827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105090264502488073611442205 39408849188433027604290827)
    ·
      refine ⟨59113273782649541406436241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39408849188433027604290827 59113273782649541406436241)
      ·
        refine ⟨44334955336987156054827181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59113273782649541406436241 44334955336987156054827181)
        ·
          refine ⟨16625608251370183520560193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44334955336987156054827181 16625608251370183520560193)
          ·
            refine ⟨12469206188527637640420145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16625608251370183520560193 12469206188527637640420145)
            ·
              refine ⟨9351904641395728230315109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12469206188527637640420145 9351904641395728230315109)
              ·
                refine ⟨1753482120261699043184083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9351904641395728230315109 1753482120261699043184083)
                ·
                  refine ⟨2630223180392548564776125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1753482120261699043184083 2630223180392548564776125)
                  ·
                    refine ⟨986333692647205711791047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2630223180392548564776125 986333692647205711791047)
                    ·
                      rfl

theorem cell22_2881317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 4, 1, 3].length) (baseStart_2881317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2881317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2881317 prefixEnd_2881317 := by exact prefixLift 2881317
  have htrace : WordTrace (prefixWord ++ tailWord_2881317) baseStart_2881317 baseEnd_2881317 := by
    simpa [prefixWord, tailWord_2881317, baseEnd_2881317] using wordTrace_append hprefix tailTrace_2881317
  have hstable : (prefixWord ++ tailWord_2881317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881317).length < 2 ^ (prefixWord ++ tailWord_2881317).sum := by decide
  have hdescent : baseEnd_2881317 < baseStart_2881317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881375 : List Nat := [1, 1, 2, 3, 1, 6, 1, 1, 6]
def baseStart_2881375 : Nat := 118140960795 + 2881375 * 2 ^ 59
def prefixEnd_2881375 : Nat := 4983230072969 + 3 ^ 40 * 2881375 * 2
def baseEnd_2881375 : Nat := 328784515744170964613623

theorem tailTrace_2881375 : CollatzResearch.WordTrace tailWord_2881375 prefixEnd_2881375 328784515744170964613623 := by
  unfold tailWord_2881375
  simp only [CollatzResearch.WordTrace]
  refine ⟨105092379936277949517053579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70061586624185299678035719 105092379936277949517053579)
  ·
    refine ⟨157638569904416924275580369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105092379936277949517053579 157638569904416924275580369)
    ·
      refine ⟨118228927428312693206685277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157638569904416924275580369 118228927428312693206685277)
      ·
        refine ⟨44335847785617259952506979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118228927428312693206685277 44335847785617259952506979)
        ·
          refine ⟨66503771678425889928760469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44335847785617259952506979 66503771678425889928760469)
          ·
            refine ⟨3117364297426213590410647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 66503771678425889928760469 3117364297426213590410647)
            ·
              refine ⟨4676046446139320385615971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3117364297426213590410647 4676046446139320385615971)
              ·
                refine ⟨7014069669208980578423957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4676046446139320385615971 7014069669208980578423957)
                ·
                  refine ⟨328784515744170964613623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7014069669208980578423957 328784515744170964613623)
                  ·
                    rfl

theorem cell22_2881375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 6].length) (baseStart_2881375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2881375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2881375 prefixEnd_2881375 := by exact prefixLift 2881375
  have htrace : WordTrace (prefixWord ++ tailWord_2881375) baseStart_2881375 baseEnd_2881375 := by
    simpa [prefixWord, tailWord_2881375, baseEnd_2881375] using wordTrace_append hprefix tailTrace_2881375
  have hstable : (prefixWord ++ tailWord_2881375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881375).length < 2 ^ (prefixWord ++ tailWord_2881375).sum := by decide
  have hdescent : baseEnd_2881375 < baseStart_2881375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881426 : List Nat := [3, 2, 3, 2, 1, 3, 2, 2, 4]
def baseStart_2881426 : Nat := 118140960795 + 2881426 * 2 ^ 59
def prefixEnd_2881426 : Nat := 4983230072969 + 3 ^ 40 * 2881426 * 2
def baseEnd_2881426 : Nat := 328790335191588586938571

theorem tailTrace_2881426 : CollatzResearch.WordTrace tailWord_2881426 prefixEnd_2881426 328790335191588586938571 := by
  unfold tailWord_2881426
  simp only [CollatzResearch.WordTrace]
  refine ⟨26273560014773296306790033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70062826706062123484773421 26273560014773296306790033)
  ·
    refine ⟨19705170011079972230092525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26273560014773296306790033 19705170011079972230092525)
    ·
      refine ⟨7389438754154989586284697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19705170011079972230092525 7389438754154989586284697)
      ·
        refine ⟨5542079065616242189713523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7389438754154989586284697 5542079065616242189713523)
        ·
          refine ⟨8313118598424363284570285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5542079065616242189713523 8313118598424363284570285)
          ·
            refine ⟨3117419474409136231713857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8313118598424363284570285 3117419474409136231713857)
            ·
              refine ⟨2338064605806852173785393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3117419474409136231713857 2338064605806852173785393)
              ·
                refine ⟨1753548454355139130339045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2338064605806852173785393 1753548454355139130339045)
                ·
                  refine ⟨328790335191588586938571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1753548454355139130339045 328790335191588586938571)
                  ·
                    rfl

theorem cell22_2881426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 2, 4].length) (baseStart_2881426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2881426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2881426 prefixEnd_2881426 := by exact prefixLift 2881426
  have htrace : WordTrace (prefixWord ++ tailWord_2881426) baseStart_2881426 baseEnd_2881426 := by
    simpa [prefixWord, tailWord_2881426, baseEnd_2881426] using wordTrace_append hprefix tailTrace_2881426
  have hstable : (prefixWord ++ tailWord_2881426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881426).length < 2 ^ (prefixWord ++ tailWord_2881426).sum := by decide
  have hdescent : baseEnd_2881426 < baseStart_2881426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881433 : List Nat := [1, 2, 1, 2, 1, 3, 3, 1, 2, 6]
def baseStart_2881433 : Nat := 118140960795 + 2881433 * 2 ^ 59
def prefixEnd_2881433 : Nat := 4983230072969 + 3 ^ 40 * 2881433 * 2
def baseEnd_2881433 : Nat := 986373401817820075890691

theorem tailTrace_2881433 : CollatzResearch.WordTrace tailWord_2881433 prefixEnd_2881433 986373401817820075890691 := by
  unfold tailWord_2881433
  simp only [CollatzResearch.WordTrace]
  refine ⟨105094495370067825422664953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70062996913378550281776635 105094495370067825422664953)
  ·
    refine ⟨78820871527550869066998715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105094495370067825422664953 78820871527550869066998715)
    ·
      refine ⟨118231307291326303600498073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78820871527550869066998715 118231307291326303600498073)
      ·
        refine ⟨88673480468494727700373555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118231307291326303600498073 88673480468494727700373555)
        ·
          refine ⟨133010220702742091550560333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88673480468494727700373555 133010220702742091550560333)
          ·
            refine ⟨49878832763528284331460125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133010220702742091550560333 49878832763528284331460125)
            ·
              refine ⟨18704562286323106624297547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49878832763528284331460125 18704562286323106624297547)
              ·
                refine ⟨28056843429484659936446321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18704562286323106624297547 28056843429484659936446321)
                ·
                  refine ⟨21042632572113494952334741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28056843429484659936446321 21042632572113494952334741)
                  ·
                    refine ⟨986373401817820075890691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21042632572113494952334741 986373401817820075890691)
                    ·
                      rfl

theorem cell22_2881433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 6].length) (baseStart_2881433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2881433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2881433 prefixEnd_2881433 := by exact prefixLift 2881433
  have htrace : WordTrace (prefixWord ++ tailWord_2881433) baseStart_2881433 baseEnd_2881433 := by
    simpa [prefixWord, tailWord_2881433, baseEnd_2881433] using wordTrace_append hprefix tailTrace_2881433
  have hstable : (prefixWord ++ tailWord_2881433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881433).length < 2 ^ (prefixWord ++ tailWord_2881433).sum := by decide
  have hdescent : baseEnd_2881433 < baseStart_2881433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881463 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 3, 7]
def baseStart_2881463 : Nat := 118140960795 + 2881463 * 2 ^ 59
def prefixEnd_2881463 : Nat := 4983230072969 + 3 ^ 40 * 2881463 * 2
def baseEnd_2881463 : Nat := 986383671430909997640599

theorem tailTrace_2881463 : CollatzResearch.WordTrace tailWord_2881463 prefixEnd_2881463 986383671430909997640599 := by
  unfold tailWord_2881463
  simp only [CollatzResearch.WordTrace]
  refine ⟨105095589559959140546257043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70063726373306093697504695 105095589559959140546257043)
  ·
    refine ⟨157643384339938710819385565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105095589559959140546257043 157643384339938710819385565)
    ·
      refine ⟨59116269127477016557269587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157643384339938710819385565 59116269127477016557269587)
      ·
        refine ⟨88674403691215524835904381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59116269127477016557269587 88674403691215524835904381)
        ·
          refine ⟨33252901384205821813464143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88674403691215524835904381 33252901384205821813464143)
          ·
            refine ⟨49879352076308732720196215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33252901384205821813464143 49879352076308732720196215)
            ·
              refine ⟨74819028114463099080294323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49879352076308732720196215 74819028114463099080294323)
              ·
                refine ⟨112228542171694648620441485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74819028114463099080294323 112228542171694648620441485)
                ·
                  refine ⟨42085703314385493232665557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112228542171694648620441485 42085703314385493232665557)
                  ·
                    refine ⟨986383671430909997640599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42085703314385493232665557 986383671430909997640599)
                    ·
                      rfl

theorem cell22_2881463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 7].length) (baseStart_2881463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2881463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2881463 prefixEnd_2881463 := by exact prefixLift 2881463
  have htrace : WordTrace (prefixWord ++ tailWord_2881463) baseStart_2881463 baseEnd_2881463 := by
    simpa [prefixWord, tailWord_2881463, baseEnd_2881463] using wordTrace_append hprefix tailTrace_2881463
  have hstable : (prefixWord ++ tailWord_2881463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881463).length < 2 ^ (prefixWord ++ tailWord_2881463).sum := by decide
  have hdescent : baseEnd_2881463 < baseStart_2881463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881469 : List Nat := [1, 4, 1, 2, 3, 1, 1, 5, 1, 3]
def baseStart_2881469 : Nat := 118140960795 + 2881469 * 2 ^ 59
def prefixEnd_2881469 : Nat := 4983230072969 + 3 ^ 40 * 2881469 * 2
def baseEnd_2881469 : Nat := 986385725353527981990581

theorem tailTrace_2881469 : CollatzResearch.WordTrace tailWord_2881469 prefixEnd_2881469 986385725353527981990581 := by
  unfold tailWord_2881469
  simp only [CollatzResearch.WordTrace]
  refine ⟨105095808397937403570975461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70063872265291602380650307 105095808397937403570975461)
  ·
    refine ⟨19705464074613263169557899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105095808397937403570975461 19705464074613263169557899)
    ·
      refine ⟨29558196111919894754336849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19705464074613263169557899 29558196111919894754336849)
      ·
        refine ⟨22168647083939921065752637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29558196111919894754336849 22168647083939921065752637)
        ·
          refine ⟨8313242656477470399657239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22168647083939921065752637 8313242656477470399657239)
          ·
            refine ⟨12469863984716205599485859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8313242656477470399657239 12469863984716205599485859)
            ·
              refine ⟨18704795977074308399228789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12469863984716205599485859 18704795977074308399228789)
              ·
                refine ⟨1753574622850716412427699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18704795977074308399228789 1753574622850716412427699)
                ·
                  refine ⟨2630361934276074618641549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1753574622850716412427699 2630361934276074618641549)
                  ·
                    refine ⟨986385725353527981990581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2630361934276074618641549 986385725353527981990581)
                    ·
                      rfl

theorem cell22_2881469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 5, 1, 3].length) (baseStart_2881469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2881469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2881469 prefixEnd_2881469 := by exact prefixLift 2881469
  have htrace : WordTrace (prefixWord ++ tailWord_2881469) baseStart_2881469 baseEnd_2881469 := by
    simpa [prefixWord, tailWord_2881469, baseEnd_2881469] using wordTrace_append hprefix tailTrace_2881469
  have hstable : (prefixWord ++ tailWord_2881469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881469).length < 2 ^ (prefixWord ++ tailWord_2881469).sum := by decide
  have hdescent : baseEnd_2881469 < baseStart_2881469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881480 : List Nat := [2, 1, 3, 1, 4, 1, 1, 2, 2, 5]
def baseStart_2881480 : Nat := 118140960795 + 2881480 * 2 ^ 59
def prefixEnd_2881480 : Nat := 4983230072969 + 3 ^ 40 * 2881480 * 2
def baseEnd_2881480 : Nat := 986389490878327619965547

theorem tailTrace_2881480 : CollatzResearch.WordTrace tailWord_2881480 prefixEnd_2881480 986389490878327619965547 := by
  unfold tailWord_2881480
  simp only [CollatzResearch.WordTrace]
  refine ⟨52548104800448776224812947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70064139733931701633083929 52548104800448776224812947)
  ·
    refine ⟨78822157200673164337219421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52548104800448776224812947 78822157200673164337219421)
    ·
      refine ⟨29558308950252436626457283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78822157200673164337219421 29558308950252436626457283)
      ·
        refine ⟨44337463425378654939685925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29558308950252436626457283 44337463425378654939685925)
        ·
          refine ⟨8313274392258497801191111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44337463425378654939685925 8313274392258497801191111)
          ·
            refine ⟨12469911588387746701786667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8313274392258497801191111 12469911588387746701786667)
            ·
              refine ⟨18704867382581620052680001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12469911588387746701786667 18704867382581620052680001)
              ·
                refine ⟨14028650536936215039510001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18704867382581620052680001 14028650536936215039510001)
                ·
                  refine ⟨10521487902702161279632501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14028650536936215039510001 10521487902702161279632501)
                  ·
                    refine ⟨986389490878327619965547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10521487902702161279632501 986389490878327619965547)
                    ·
                      rfl

theorem cell22_2881480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_2881480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2881480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2881480 prefixEnd_2881480 := by exact prefixLift 2881480
  have htrace : WordTrace (prefixWord ++ tailWord_2881480) baseStart_2881480 baseEnd_2881480 := by
    simpa [prefixWord, tailWord_2881480, baseEnd_2881480] using wordTrace_append hprefix tailTrace_2881480
  have hstable : (prefixWord ++ tailWord_2881480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881480).length < 2 ^ (prefixWord ++ tailWord_2881480).sum := by decide
  have hdescent : baseEnd_2881480 < baseStart_2881480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881544 : List Nat := [2, 1, 3, 2, 1, 2, 5, 2, 4]
def baseStart_2881544 : Nat := 118140960795 + 2881544 * 2 ^ 59
def prefixEnd_2881544 : Nat := 4983230072969 + 3 ^ 40 * 2881544 * 2
def baseEnd_2881544 : Nat := 328803799795417595455117

theorem tailTrace_2881544 : CollatzResearch.WordTrace tailWord_2881544 prefixEnd_2881544 328803799795417595455117 := by
  unfold tailWord_2881544
  simp only [CollatzResearch.WordTrace]
  refine ⟨52549271936332845689977843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70065695915110460919970457 52549271936332845689977843)
  ·
    refine ⟨78823907904499268534966765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52549271936332845689977843 78823907904499268534966765)
    ·
      refine ⟨29558965464187225700612537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78823907904499268534966765 29558965464187225700612537)
      ·
        refine ⟨22169224098140419275459403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29558965464187225700612537 22169224098140419275459403)
        ·
          refine ⟨33253836147210628913189105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22169224098140419275459403 33253836147210628913189105)
          ·
            refine ⟨24940377110407971684891829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33253836147210628913189105 24940377110407971684891829)
            ·
              refine ⟨2338160354100747345458609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24940377110407971684891829 2338160354100747345458609)
              ·
                refine ⟨1753620265575560509093957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2338160354100747345458609 1753620265575560509093957)
                ·
                  refine ⟨328803799795417595455117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1753620265575560509093957 328803799795417595455117)
                  ·
                    rfl

theorem cell22_2881544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 2, 4].length) (baseStart_2881544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2881544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2881544 prefixEnd_2881544 := by exact prefixLift 2881544
  have htrace : WordTrace (prefixWord ++ tailWord_2881544) baseStart_2881544 baseEnd_2881544 := by
    simpa [prefixWord, tailWord_2881544, baseEnd_2881544] using wordTrace_append hprefix tailTrace_2881544
  have hstable : (prefixWord ++ tailWord_2881544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881544).length < 2 ^ (prefixWord ++ tailWord_2881544).sum := by decide
  have hdescent : baseEnd_2881544 < baseStart_2881544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881615 : List Nat := [1, 1, 2, 1, 1, 2, 2, 5, 2, 5]
def baseStart_2881615 : Nat := 118140960795 + 2881615 * 2 ^ 59
def prefixEnd_2881615 : Nat := 4983230072969 + 3 ^ 40 * 2881615 * 2
def baseEnd_2881615 : Nat := 986435704137232267840133

theorem tailTrace_2881615 : CollatzResearch.WordTrace tailWord_2881615 prefixEnd_2881615 986435704137232267840133 := by
  unfold tailWord_2881615
  simp only [CollatzResearch.WordTrace]
  refine ⟨105101133455408470505790299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70067422303605647003860199 105101133455408470505790299)
  ·
    refine ⟨157651700183112705758685449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105101133455408470505790299 157651700183112705758685449)
    ·
      refine ⟨118238775137334529319014087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157651700183112705758685449 118238775137334529319014087)
      ·
        refine ⟨177358162706001793978521131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118238775137334529319014087 177358162706001793978521131)
        ·
          refine ⟨266037244059002690967781697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177358162706001793978521131 266037244059002690967781697)
          ·
            refine ⟨199527933044252018225836273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266037244059002690967781697 199527933044252018225836273)
            ·
              refine ⟨149645949783189013669377205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199527933044252018225836273 149645949783189013669377205)
              ·
                refine ⟨14029307792173970031504113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 149645949783189013669377205 14029307792173970031504113)
                ·
                  refine ⟨10521980844130477523628085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14029307792173970031504113 10521980844130477523628085)
                  ·
                    refine ⟨986435704137232267840133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10521980844130477523628085 986435704137232267840133)
                    ·
                      rfl

theorem cell22_2881615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 5].length) (baseStart_2881615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2881615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2881615 prefixEnd_2881615 := by exact prefixLift 2881615
  have htrace : WordTrace (prefixWord ++ tailWord_2881615) baseStart_2881615 baseEnd_2881615 := by
    simpa [prefixWord, tailWord_2881615, baseEnd_2881615] using wordTrace_append hprefix tailTrace_2881615
  have hstable : (prefixWord ++ tailWord_2881615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881615).length < 2 ^ (prefixWord ++ tailWord_2881615).sum := by decide
  have hdescent : baseEnd_2881615 < baseStart_2881615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881692 : List Nat := [2, 2, 3, 2, 1, 1, 1, 3, 1, 6]
def baseStart_2881692 : Nat := 118140960795 + 2881692 * 2 ^ 59
def prefixEnd_2881692 : Nat := 4983230072969 + 3 ^ 40 * 2881692 * 2
def baseEnd_2881692 : Nat := 986462062810829733664897

theorem tailTrace_2881692 : CollatzResearch.WordTrace tailWord_2881692 prefixEnd_2881692 986462062810829733664897 := by
  unfold tailWord_2881692
  simp only [CollatzResearch.WordTrace]
  refine ⟨52551970938064756328171665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70069294584086341770895553 52551970938064756328171665)
  ·
    refine ⟨39413978203548567246128749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52551970938064756328171665 39413978203548567246128749)
    ·
      refine ⟨14780241826330712717298281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39413978203548567246128749 14780241826330712717298281)
      ·
        refine ⟨11085181369748034537973711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14780241826330712717298281 11085181369748034537973711)
        ·
          refine ⟨16627772054622051806960567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11085181369748034537973711 16627772054622051806960567)
          ·
            refine ⟨24941658081933077710440851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16627772054622051806960567 24941658081933077710440851)
            ·
              refine ⟨37412487122899616565661277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24941658081933077710440851 37412487122899616565661277)
              ·
                refine ⟨14029682671087356212122979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37412487122899616565661277 14029682671087356212122979)
                ·
                  refine ⟨21044524006631034318184469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14029682671087356212122979 21044524006631034318184469)
                  ·
                    refine ⟨986462062810829733664897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21044524006631034318184469 986462062810829733664897)
                    ·
                      rfl

theorem cell22_2881692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_2881692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2881692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2881692 prefixEnd_2881692 := by exact prefixLift 2881692
  have htrace : WordTrace (prefixWord ++ tailWord_2881692) baseStart_2881692 baseEnd_2881692 := by
    simpa [prefixWord, tailWord_2881692, baseEnd_2881692] using wordTrace_append hprefix tailTrace_2881692
  have hstable : (prefixWord ++ tailWord_2881692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881692).length < 2 ^ (prefixWord ++ tailWord_2881692).sum := by decide
  have hdescent : baseEnd_2881692 < baseStart_2881692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881696 : List Nat := [2, 1, 1, 4, 2, 4, 1, 3, 4]
def baseStart_2881696 : Nat := 118140960795 + 2881696 * 2 ^ 59
def prefixEnd_2881696 : Nat := 4983230072969 + 3 ^ 40 * 2881696 * 2
def baseEnd_2881696 : Nat := 328821144030858352188295

theorem tailTrace_2881696 : CollatzResearch.WordTrace tailWord_2881696 prefixEnd_2881696 328821144030858352188295 := by
  unfold tailWord_2881696
  simp only [CollatzResearch.WordTrace]
  refine ⟨52552043884057510669744471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70069391845410014226325961 52552043884057510669744471)
  ·
    refine ⟨78828065826086266004616707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52552043884057510669744471 78828065826086266004616707)
    ·
      refine ⟨118242098739129399006925061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78828065826086266004616707 118242098739129399006925061)
      ·
        refine ⟨22170393513586762313798449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118242098739129399006925061 22170393513586762313798449)
        ·
          refine ⟨16627795135190071735348837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22170393513586762313798449 16627795135190071735348837)
          ·
            refine ⟨3117711587848138450377907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16627795135190071735348837 3117711587848138450377907)
            ·
              refine ⟨4676567381772207675566861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3117711587848138450377907 4676567381772207675566861)
              ·
                refine ⟨1753712768164577878337573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4676567381772207675566861 1753712768164577878337573)
                ·
                  refine ⟨328821144030858352188295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1753712768164577878337573 328821144030858352188295)
                  ·
                    rfl

theorem cell22_2881696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 3, 4].length) (baseStart_2881696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2881696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2881696 prefixEnd_2881696 := by exact prefixLift 2881696
  have htrace : WordTrace (prefixWord ++ tailWord_2881696) baseStart_2881696 baseEnd_2881696 := by
    simpa [prefixWord, tailWord_2881696, baseEnd_2881696] using wordTrace_append hprefix tailTrace_2881696
  have hstable : (prefixWord ++ tailWord_2881696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881696).length < 2 ^ (prefixWord ++ tailWord_2881696).sum := by decide
  have hdescent : baseEnd_2881696 < baseStart_2881696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881709 : List Nat := [1, 5, 2, 1, 2, 1, 1, 1, 4, 4]
def baseStart_2881709 : Nat := 118140960795 + 2881709 * 2 ^ 59
def prefixEnd_2881709 : Nat := 4983230072969 + 3 ^ 40 * 2881709 * 2
def baseEnd_2881709 : Nat := 986467882258247355989845

theorem tailTrace_2881709 : CollatzResearch.WordTrace tailWord_2881709 prefixEnd_2881709 986467882258247355989845 := by
  unfold tailWord_2881709
  simp only [CollatzResearch.WordTrace]
  refine ⟨105104561917067924559712181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70069707944711949706474787 105104561917067924559712181)
  ·
    refine ⟨9853552679725117927473017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105104561917067924559712181 9853552679725117927473017)
    ·
      refine ⟨7390164509793838445604763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9853552679725117927473017 7390164509793838445604763)
      ·
        refine ⟨11085246764690757668407145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7390164509793838445604763 11085246764690757668407145)
        ·
          refine ⟨8313935073518068251305359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11085246764690757668407145 8313935073518068251305359)
          ·
            refine ⟨12470902610277102376958039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8313935073518068251305359 12470902610277102376958039)
            ·
              refine ⟨18706353915415653565437059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12470902610277102376958039 18706353915415653565437059)
              ·
                refine ⟨28059530873123480348155589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18706353915415653565437059 28059530873123480348155589)
                ·
                  refine ⟨5261162038710652565279173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28059530873123480348155589 5261162038710652565279173)
                  ·
                    refine ⟨986467882258247355989845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5261162038710652565279173 986467882258247355989845)
                    ·
                      rfl

theorem cell22_2881709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_2881709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2881709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2881709 prefixEnd_2881709 := by exact prefixLift 2881709
  have htrace : WordTrace (prefixWord ++ tailWord_2881709) baseStart_2881709 baseEnd_2881709 := by
    simpa [prefixWord, tailWord_2881709, baseEnd_2881709] using wordTrace_append hprefix tailTrace_2881709
  have hstable : (prefixWord ++ tailWord_2881709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881709).length < 2 ^ (prefixWord ++ tailWord_2881709).sum := by decide
  have hdescent : baseEnd_2881709 < baseStart_2881709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881713 : List Nat := [1, 2, 2, 5, 2, 1, 3, 2, 4]
def baseStart_2881713 : Nat := 118140960795 + 2881713 * 2 ^ 59
def prefixEnd_2881713 : Nat := 4983230072969 + 3 ^ 40 * 2881713 * 2
def baseEnd_2881713 : Nat := 328823083846664226296611

theorem tailTrace_2881713 : CollatzResearch.WordTrace tailWord_2881713 prefixEnd_2881713 328823083846664226296611 := by
  unfold tailWord_2881713
  simp only [CollatzResearch.WordTrace]
  refine ⟨105104707809053433242857793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70069805206035622161905195 105104707809053433242857793)
  ·
    refine ⟨78828530856790074932143345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105104707809053433242857793 78828530856790074932143345)
    ·
      refine ⟨59121398142592556199107509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78828530856790074932143345 59121398142592556199107509)
      ·
        refine ⟨5542631075868052143666329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59121398142592556199107509 5542631075868052143666329)
        ·
          refine ⟨4156973306901039107749747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5542631075868052143666329 4156973306901039107749747)
          ·
            refine ⟨6235459960351558661624621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4156973306901039107749747 6235459960351558661624621)
            ·
              refine ⟨2338297485131834498109233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6235459960351558661624621 2338297485131834498109233)
              ·
                refine ⟨1753723113848875873581925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2338297485131834498109233 1753723113848875873581925)
                ·
                  refine ⟨328823083846664226296611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1753723113848875873581925 328823083846664226296611)
                  ·
                    rfl

theorem cell22_2881713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 2, 4].length) (baseStart_2881713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2881713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2881713 prefixEnd_2881713 := by exact prefixLift 2881713
  have htrace : WordTrace (prefixWord ++ tailWord_2881713) baseStart_2881713 baseEnd_2881713 := by
    simpa [prefixWord, tailWord_2881713, baseEnd_2881713] using wordTrace_append hprefix tailTrace_2881713
  have hstable : (prefixWord ++ tailWord_2881713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881713).length < 2 ^ (prefixWord ++ tailWord_2881713).sum := by decide
  have hdescent : baseEnd_2881713 < baseStart_2881713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881724 : List Nat := [2, 2, 2, 3, 3, 1, 2, 7]
def baseStart_2881724 : Nat := 118140960795 + 2881724 * 2 ^ 59
def prefixEnd_2881724 : Nat := 4983230072969 + 3 ^ 40 * 2881724 * 2
def baseEnd_2881724 : Nat := 109608113007199146318311

theorem tailTrace_2881724 : CollatzResearch.WordTrace tailWord_2881724 prefixEnd_2881724 109608113007199146318311 := by
  unfold tailWord_2881724
  simp only [CollatzResearch.WordTrace]
  refine ⟨52552554506006791060754113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70070072674675721414338817 52552554506006791060754113)
  ·
    refine ⟨39414415879505093295565585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52552554506006791060754113 39414415879505093295565585)
    ·
      refine ⟨29560811909628819971674189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39414415879505093295565585 29560811909628819971674189)
      ·
        refine ⟨11085304466110807489377821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29560811909628819971674189 11085304466110807489377821)
        ·
          refine ⟨4156989174791552808516683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11085304466110807489377821 4156989174791552808516683)
          ·
            refine ⟨6235483762187329212775025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4156989174791552808516683 6235483762187329212775025)
            ·
              refine ⟨4676612821640496909581269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6235483762187329212775025 4676612821640496909581269)
              ·
                refine ⟨109608113007199146318311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4676612821640496909581269 109608113007199146318311)
                ·
                  rfl

theorem cell22_2881724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 7].length) (baseStart_2881724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2881724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2881724 prefixEnd_2881724 := by exact prefixLift 2881724
  have htrace : WordTrace (prefixWord ++ tailWord_2881724) baseStart_2881724 baseEnd_2881724 := by
    simpa [prefixWord, tailWord_2881724, baseEnd_2881724] using wordTrace_append hprefix tailTrace_2881724
  have hstable : (prefixWord ++ tailWord_2881724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881724).length < 2 ^ (prefixWord ++ tailWord_2881724).sum := by decide
  have hdescent : baseEnd_2881724 < baseStart_2881724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881728 : List Nat := [2, 1, 1, 2, 5, 3, 2, 1, 2, 3]
def baseStart_2881728 : Nat := 118140960795 + 2881728 * 2 ^ 59
def prefixEnd_2881728 : Nat := 4983230072969 + 3 ^ 40 * 2881728 * 2
def baseEnd_2881728 : Nat := 986474386346537639764787

theorem tailTrace_2881728 : CollatzResearch.WordTrace tailWord_2881728 prefixEnd_2881728 986474386346537639764787 := by
  unfold tailWord_2881728
  simp only [CollatzResearch.WordTrace]
  refine ⟨52552627451999545402326919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70070169935999393869769225 52552627451999545402326919)
  ·
    refine ⟨78828941177999318103490379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52552627451999545402326919 78828941177999318103490379)
    ·
      refine ⟨118243411766998977155235569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78828941177999318103490379 118243411766998977155235569)
      ·
        refine ⟨88682558825249232866426677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118243411766998977155235569 88682558825249232866426677)
        ·
          refine ⟨8313989889867115581227501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88682558825249232866426677 8313989889867115581227501)
          ·
            refine ⟨3117746208700168342960313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8313989889867115581227501 3117746208700168342960313)
            ·
              refine ⟨2338309656525126257220235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3117746208700168342960313 2338309656525126257220235)
              ·
                refine ⟨3507464484787689385830353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2338309656525126257220235 3507464484787689385830353)
                ·
                  refine ⟨2630598363590767039372765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3507464484787689385830353 2630598363590767039372765)
                  ·
                    refine ⟨986474386346537639764787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2630598363590767039372765 986474386346537639764787)
                    ·
                      rfl

theorem cell22_2881728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 1, 2, 3].length) (baseStart_2881728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2881728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2881728 prefixEnd_2881728 := by exact prefixLift 2881728
  have htrace : WordTrace (prefixWord ++ tailWord_2881728) baseStart_2881728 baseEnd_2881728 := by
    simpa [prefixWord, tailWord_2881728, baseEnd_2881728] using wordTrace_append hprefix tailTrace_2881728
  have hstable : (prefixWord ++ tailWord_2881728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881728).length < 2 ^ (prefixWord ++ tailWord_2881728).sum := by decide
  have hdescent : baseEnd_2881728 < baseStart_2881728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881762 : List Nat := [3, 3, 4, 1, 1, 1, 2, 2, 2, 3]
def baseStart_2881762 : Nat := 118140960795 + 2881762 * 2 ^ 59
def prefixEnd_2881762 : Nat := 4983230072969 + 3 ^ 40 * 2881762 * 2
def baseEnd_2881762 : Nat := 986486025241372884414683

theorem tailTrace_2881762 : CollatzResearch.WordTrace tailWord_2881762 prefixEnd_2881762 986486025241372884414683 := by
  unfold tailWord_2881762
  simp only [CollatzResearch.WordTrace]
  refine ⟨26276623746468978652847885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70070996657250609740927693 26276623746468978652847885)
  ·
    refine ⟨9853733904925866994817957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26276623746468978652847885 9853733904925866994817957)
    ·
      refine ⟨1847575107173600061528367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9853733904925866994817957 1847575107173600061528367)
      ·
        refine ⟨2771362660760400092292551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1847575107173600061528367 2771362660760400092292551)
        ·
          refine ⟨4157043991140600138438827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2771362660760400092292551 4157043991140600138438827)
          ·
            refine ⟨6235565986710900207658241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4157043991140600138438827 6235565986710900207658241)
            ·
              refine ⟨4676674490033175155743681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6235565986710900207658241 4676674490033175155743681)
              ·
                refine ⟨3507505867524881366807761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4676674490033175155743681 3507505867524881366807761)
                ·
                  refine ⟨2630629400643661025105821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3507505867524881366807761 2630629400643661025105821)
                  ·
                    refine ⟨986486025241372884414683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2630629400643661025105821 986486025241372884414683)
                    ·
                      rfl

theorem cell22_2881762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_2881762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2881762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2881762 prefixEnd_2881762 := by exact prefixLift 2881762
  have htrace : WordTrace (prefixWord ++ tailWord_2881762) baseStart_2881762 baseEnd_2881762 := by
    simpa [prefixWord, tailWord_2881762, baseEnd_2881762] using wordTrace_append hprefix tailTrace_2881762
  have hstable : (prefixWord ++ tailWord_2881762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881762).length < 2 ^ (prefixWord ++ tailWord_2881762).sum := by decide
  have hdescent : baseEnd_2881762 < baseStart_2881762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881859 : List Nat := [1, 1, 1, 3, 1, 3, 6, 6]
def baseStart_2881859 : Nat := 118140960795 + 2881859 * 2 ^ 59
def prefixEnd_2881859 : Nat := 4983230072969 + 3 ^ 40 * 2881859 * 2
def baseEnd_2881859 : Nat := 109613247813744107193265

theorem tailTrace_2881859 : CollatzResearch.WordTrace tailWord_2881859 prefixEnd_2881859 109613247813744107193265 := by
  unfold tailWord_2881859
  simp only [CollatzResearch.WordTrace]
  refine ⟨105110032866524500177672631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70073355244349666785115087 105110032866524500177672631)
  ·
    refine ⟨157665049299786750266508947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105110032866524500177672631 157665049299786750266508947)
    ·
      refine ⟨236497573949680125399763421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157665049299786750266508947 236497573949680125399763421)
      ·
        refine ⟨88686590231130047024911283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236497573949680125399763421 88686590231130047024911283)
        ·
          refine ⟨133029885346695070537366925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88686590231130047024911283 133029885346695070537366925)
          ·
            refine ⟨49886207005010651451512597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133029885346695070537366925 49886207005010651451512597)
            ·
              refine ⟨2338415953359874286789653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 49886207005010651451512597 2338415953359874286789653)
              ·
                refine ⟨109613247813744107193265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2338415953359874286789653 109613247813744107193265)
                ·
                  rfl

theorem cell22_2881859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 6].length) (baseStart_2881859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2881859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2881859 prefixEnd_2881859 := by exact prefixLift 2881859
  have htrace : WordTrace (prefixWord ++ tailWord_2881859) baseStart_2881859 baseEnd_2881859 := by
    simpa [prefixWord, tailWord_2881859, baseEnd_2881859] using wordTrace_append hprefix tailTrace_2881859
  have hstable : (prefixWord ++ tailWord_2881859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881859).length < 2 ^ (prefixWord ++ tailWord_2881859).sum := by decide
  have hdescent : baseEnd_2881859 < baseStart_2881859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881953 : List Nat := [1, 2, 3, 5, 1, 1, 1, 1, 2, 5]
def baseStart_2881953 : Nat := 118140960795 + 2881953 * 2 ^ 59
def prefixEnd_2881953 : Nat := 4983230072969 + 3 ^ 40 * 2881953 * 2
def baseEnd_2881953 : Nat := 986551408444712052889097

theorem tailTrace_2881953 : CollatzResearch.WordTrace tailWord_2881953 prefixEnd_2881953 986551408444712052889097 := by
  unfold tailWord_2881953
  simp only [CollatzResearch.WordTrace]
  refine ⟨105113461328183954231594513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70075640885455969487729675 105113461328183954231594513)
  ·
    refine ⟨78835095996137965673695885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105113461328183954231594513 78835095996137965673695885)
    ·
      refine ⟨29563160998551737127635957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78835095996137965673695885 29563160998551737127635957)
      ·
        refine ⟨2771546343614225355715871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29563160998551737127635957 2771546343614225355715871)
        ·
          refine ⟨4157319515421338033573807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2771546343614225355715871 4157319515421338033573807)
          ·
            refine ⟨6235979273132007050360711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4157319515421338033573807 6235979273132007050360711)
            ·
              refine ⟨9353968909698010575541067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6235979273132007050360711 9353968909698010575541067)
              ·
                refine ⟨14030953364547015863311601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9353968909698010575541067 14030953364547015863311601)
                ·
                  refine ⟨10523215023410261897483701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14030953364547015863311601 10523215023410261897483701)
                  ·
                    refine ⟨986551408444712052889097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10523215023410261897483701 986551408444712052889097)
                    ·
                      rfl

theorem cell22_2881953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 5].length) (baseStart_2881953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2881953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2881953 prefixEnd_2881953 := by exact prefixLift 2881953
  have htrace : WordTrace (prefixWord ++ tailWord_2881953) baseStart_2881953 baseEnd_2881953 := by
    simpa [prefixWord, tailWord_2881953, baseEnd_2881953] using wordTrace_append hprefix tailTrace_2881953
  have hstable : (prefixWord ++ tailWord_2881953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881953).length < 2 ^ (prefixWord ++ tailWord_2881953).sum := by decide
  have hdescent : baseEnd_2881953 < baseStart_2881953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881979 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 8, 4]
def baseStart_2881979 : Nat := 118140960795 + 2881979 * 2 ^ 59
def prefixEnd_2881979 : Nat := 4983230072969 + 3 ^ 40 * 2881979 * 2
def baseEnd_2881979 : Nat := 986560308776056651739017

theorem tailTrace_2881979 : CollatzResearch.WordTrace tailWord_2881979 prefixEnd_2881979 986560308776056651739017 := by
  unfold tailWord_2881979
  simp only [CollatzResearch.WordTrace]
  refine ⟨105114409626089760672040991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70076273084059840448027327 105114409626089760672040991)
  ·
    refine ⟨157671614439134641008061487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105114409626089760672040991 157671614439134641008061487)
    ·
      refine ⟨236507421658701961512092231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157671614439134641008061487 236507421658701961512092231)
      ·
        refine ⟨354761132488052942268138347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236507421658701961512092231 354761132488052942268138347)
        ·
          refine ⟨532141698732079413402207521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354761132488052942268138347 532141698732079413402207521)
          ·
            refine ⟨399106274049059560051655641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 532141698732079413402207521 399106274049059560051655641)
            ·
              refine ⟨299329705536794670038741731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 399106274049059560051655641 299329705536794670038741731)
              ·
                refine ⟨448994558305192005058112597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 299329705536794670038741731 448994558305192005058112597)
                ·
                  refine ⟨5261654980138968809274757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 448994558305192005058112597 5261654980138968809274757)
                  ·
                    refine ⟨986560308776056651739017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5261654980138968809274757 986560308776056651739017)
                    ·
                      rfl

theorem cell22_2881979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 8, 4].length) (baseStart_2881979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2881979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2881979 prefixEnd_2881979 := by exact prefixLift 2881979
  have htrace : WordTrace (prefixWord ++ tailWord_2881979) baseStart_2881979 baseEnd_2881979 := by
    simpa [prefixWord, tailWord_2881979, baseEnd_2881979] using wordTrace_append hprefix tailTrace_2881979
  have hstable : (prefixWord ++ tailWord_2881979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881979).length < 2 ^ (prefixWord ++ tailWord_2881979).sum := by decide
  have hdescent : baseEnd_2881979 < baseStart_2881979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881981 : List Nat := [1, 4, 1, 2, 2, 2, 2, 2, 1, 5]
def baseStart_2881981 : Nat := 118140960795 + 2881981 * 2 ^ 59
def prefixEnd_2881981 : Nat := 4983230072969 + 3 ^ 40 * 2881981 * 2
def baseEnd_2881981 : Nat := 986560993416929313189011

theorem tailTrace_2881981 : CollatzResearch.WordTrace tailWord_2881981 prefixEnd_2881981 986560993416929313189011 := by
  unfold tailWord_2881981
  simp only [CollatzResearch.WordTrace]
  refine ⟨105114482572082515013613797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70076321714721676675742531 105114482572082515013613797)
  ·
    refine ⟨19708965482265471565052587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105114482572082515013613797 19708965482265471565052587)
    ·
      refine ⟨29563448223398207347578881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19708965482265471565052587 29563448223398207347578881)
      ·
        refine ⟨22172586167548655510684161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29563448223398207347578881 22172586167548655510684161)
        ·
          refine ⟨16629439625661491633013121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22172586167548655510684161 16629439625661491633013121)
          ·
            refine ⟨12472079719246118724759841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16629439625661491633013121 12472079719246118724759841)
            ·
              refine ⟨9354059789434589043569881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12472079719246118724759841 9354059789434589043569881)
              ·
                refine ⟨7015544842075941782677411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9354059789434589043569881 7015544842075941782677411)
                ·
                  refine ⟨10523317263113912674016117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7015544842075941782677411 10523317263113912674016117)
                  ·
                    refine ⟨986560993416929313189011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10523317263113912674016117 986560993416929313189011)
                    ·
                      rfl

theorem cell22_2881981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_2881981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2881981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2881981 prefixEnd_2881981 := by exact prefixLift 2881981
  have htrace : WordTrace (prefixWord ++ tailWord_2881981) baseStart_2881981 baseEnd_2881981 := by
    simpa [prefixWord, tailWord_2881981, baseEnd_2881981] using wordTrace_append hprefix tailTrace_2881981
  have hstable : (prefixWord ++ tailWord_2881981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881981).length < 2 ^ (prefixWord ++ tailWord_2881981).sum := by decide
  have hdescent : baseEnd_2881981 < baseStart_2881981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2881994 : List Nat := [3, 1, 2, 1, 2, 2, 11]
def baseStart_2881994 : Nat := 118140960795 + 2881994 * 2 ^ 59
def prefixEnd_2881994 : Nat := 4983230072969 + 3 ^ 40 * 2881994 * 2
def baseEnd_2881994 : Nat := 36539460873429689356073

theorem tailTrace_2881994 : CollatzResearch.WordTrace tailWord_2881994 prefixEnd_2881994 36539460873429689356073 := by
  unfold tailWord_2881994
  simp only [CollatzResearch.WordTrace]
  refine ⟨26278739180258854558459259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70076637814023612155891357 26278739180258854558459259)
  ·
    refine ⟨39418108770388281837688889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26278739180258854558459259 39418108770388281837688889)
    ·
      refine ⟨29563581577791211378266667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39418108770388281837688889 29563581577791211378266667)
      ·
        refine ⟨44345372366686817067400001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29563581577791211378266667 44345372366686817067400001)
        ·
          refine ⟨33259029275015112800550001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44345372366686817067400001 33259029275015112800550001)
          ·
            refine ⟨24944271956261334600412501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33259029275015112800550001 24944271956261334600412501)
            ·
              refine ⟨36539460873429689356073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 24944271956261334600412501 36539460873429689356073)
              ·
                rfl

theorem cell22_2881994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 11].length) (baseStart_2881994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2881994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2881994 prefixEnd_2881994 := by exact prefixLift 2881994
  have htrace : WordTrace (prefixWord ++ tailWord_2881994) baseStart_2881994 baseEnd_2881994 := by
    simpa [prefixWord, tailWord_2881994, baseEnd_2881994] using wordTrace_append hprefix tailTrace_2881994
  have hstable : (prefixWord ++ tailWord_2881994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2881994).length < 2 ^ (prefixWord ++ tailWord_2881994).sum := by decide
  have hdescent : baseEnd_2881994 < baseStart_2881994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2881994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882015 : List Nat := [1, 1, 2, 3, 3, 3, 3, 1, 2, 3]
def baseStart_2882015 : Nat := 118140960795 + 2882015 * 2 ^ 59
def prefixEnd_2882015 : Nat := 4983230072969 + 3 ^ 40 * 2882015 * 2
def baseEnd_2882015 : Nat := 986572632311764557838907

theorem tailTrace_2882015 : CollatzResearch.WordTrace tailWord_2882015 prefixEnd_2882015 986572632311764557838907 := by
  unfold tailWord_2882015
  simp only [CollatzResearch.WordTrace]
  refine ⟨105115722653959338820351499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70077148435972892546900999 105115722653959338820351499)
  ·
    refine ⟨157673583980939008230527249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105115722653959338820351499 157673583980939008230527249)
    ·
      refine ⟨118255187985704256172895437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157673583980939008230527249 118255187985704256172895437)
      ·
        refine ⟨44345695494639096064835789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118255187985704256172895437 44345695494639096064835789)
        ·
          refine ⟨16629635810489661024313421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44345695494639096064835789 16629635810489661024313421)
          ·
            refine ⟨6236113428933622884117533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16629635810489661024313421 6236113428933622884117533)
            ·
              refine ⟨2338542535850108581544075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6236113428933622884117533 2338542535850108581544075)
              ·
                refine ⟨3507813803775162872316113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2338542535850108581544075 3507813803775162872316113)
                ·
                  refine ⟨2630860352831372154237085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3507813803775162872316113 2630860352831372154237085)
                  ·
                    refine ⟨986572632311764557838907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2630860352831372154237085 986572632311764557838907)
                    ·
                      rfl

theorem cell22_2882015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 1, 2, 3].length) (baseStart_2882015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2882015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2882015 prefixEnd_2882015 := by exact prefixLift 2882015
  have htrace : WordTrace (prefixWord ++ tailWord_2882015) baseStart_2882015 baseEnd_2882015 := by
    simpa [prefixWord, tailWord_2882015, baseEnd_2882015] using wordTrace_append hprefix tailTrace_2882015
  have hstable : (prefixWord ++ tailWord_2882015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882015).length < 2 ^ (prefixWord ++ tailWord_2882015).sum := by decide
  have hdescent : baseEnd_2882015 < baseStart_2882015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882056 : List Nat := [2, 1, 3, 2, 1, 1, 1, 6, 5]
def baseStart_2882056 : Nat := 118140960795 + 2882056 * 2 ^ 59
def prefixEnd_2882056 : Nat := 4983230072969 + 3 ^ 40 * 2882056 * 2
def baseEnd_2882056 : Nat := 328862222483218039187927

theorem tailTrace_2882056 : CollatzResearch.WordTrace tailWord_2882056 prefixEnd_2882056 328862222483218039187927 := by
  unfold tailWord_2882056
  simp only [CollatzResearch.WordTrace]
  refine ⟨52558609023405401411297011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70078145364540535215062681 52558609023405401411297011)
  ·
    refine ⟨78837913535108102116945517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52558609023405401411297011 78837913535108102116945517)
    ·
      refine ⟨29564217575665538293854569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78837913535108102116945517 29564217575665538293854569)
      ·
        refine ⟨22173163181749153720390927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29564217575665538293854569 22173163181749153720390927)
        ·
          refine ⟨33259744772623730580586391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22173163181749153720390927 33259744772623730580586391)
          ·
            refine ⟨49889617158935595870879587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33259744772623730580586391 49889617158935595870879587)
            ·
              refine ⟨74834425738403393806319381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49889617158935595870879587 74834425738403393806319381)
              ·
                refine ⟨3507863706487659084671221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 74834425738403393806319381 3507863706487659084671221)
                ·
                  refine ⟨328862222483218039187927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3507863706487659084671221 328862222483218039187927)
                  ·
                    rfl

theorem cell22_2882056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 6, 5].length) (baseStart_2882056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2882056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2882056 prefixEnd_2882056 := by exact prefixLift 2882056
  have htrace : WordTrace (prefixWord ++ tailWord_2882056) baseStart_2882056 baseEnd_2882056 := by
    simpa [prefixWord, tailWord_2882056, baseEnd_2882056] using wordTrace_append hprefix tailTrace_2882056
  have hstable : (prefixWord ++ tailWord_2882056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882056).length < 2 ^ (prefixWord ++ tailWord_2882056).sum := by decide
  have hdescent : baseEnd_2882056 < baseStart_2882056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882060 : List Nat := [2, 2, 1, 2, 4, 3, 1, 1, 3, 3]
def baseStart_2882060 : Nat := 118140960795 + 2882060 * 2 ^ 59
def prefixEnd_2882060 : Nat := 4983230072969 + 3 ^ 40 * 2882060 * 2
def baseEnd_2882060 : Nat := 986588036731399440463769

theorem tailTrace_2882060 : CollatzResearch.WordTrace tailWord_2882060 prefixEnd_2882060 986588036731399440463769 := by
  unfold tailWord_2882060
  simp only [CollatzResearch.WordTrace]
  refine ⟨52558681969398155752869817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70078242625864207670493089 52558681969398155752869817)
  ·
    refine ⟨39419011477048616814652363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52558681969398155752869817 39419011477048616814652363)
    ·
      refine ⟨59128517215572925221978545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39419011477048616814652363 59128517215572925221978545)
      ·
        refine ⟨44346387911679693916483909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59128517215572925221978545 44346387911679693916483909)
        ·
          refine ⟨8314947733439942609340733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44346387911679693916483909 8314947733439942609340733)
          ·
            refine ⟨3118105400039978478502775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8314947733439942609340733 3118105400039978478502775)
            ·
              refine ⟨4677158100059967717754163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3118105400039978478502775 4677158100059967717754163)
              ·
                refine ⟨7015737150089951576631245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4677158100059967717754163 7015737150089951576631245)
                ·
                  refine ⟨2630901431283731841236717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7015737150089951576631245 2630901431283731841236717)
                  ·
                    refine ⟨986588036731399440463769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2630901431283731841236717 986588036731399440463769)
                    ·
                      rfl

theorem cell22_2882060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 3, 3].length) (baseStart_2882060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2882060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2882060 prefixEnd_2882060 := by exact prefixLift 2882060
  have htrace : WordTrace (prefixWord ++ tailWord_2882060) baseStart_2882060 baseEnd_2882060 := by
    simpa [prefixWord, tailWord_2882060, baseEnd_2882060] using wordTrace_append hprefix tailTrace_2882060
  have hstable : (prefixWord ++ tailWord_2882060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882060).length < 2 ^ (prefixWord ++ tailWord_2882060).sum := by decide
  have hdescent : baseEnd_2882060 < baseStart_2882060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882152 : List Nat := [2, 1, 4, 3, 2, 1, 2, 3, 4]
def baseStart_2882152 : Nat := 118140960795 + 2882152 * 2 ^ 59
def prefixEnd_2882152 : Nat := 4983230072969 + 3 ^ 40 * 2882152 * 2
def baseEnd_2882152 : Nat := 328873176737180622387829

theorem tailTrace_2882152 : CollatzResearch.WordTrace tailWord_2882152 prefixEnd_2882152 328873176737180622387829 := by
  unfold tailWord_2882152
  simp only [CollatzResearch.WordTrace]
  refine ⟨52560359727231505609044355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70080479636308674145392473 52560359727231505609044355)
  ·
    refine ⟨78840539590847258413566533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52560359727231505609044355 78840539590847258413566533)
    ·
      refine ⟨14782601173283860952543725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78840539590847258413566533 14782601173283860952543725)
      ·
        refine ⟨5543475439981447857203897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14782601173283860952543725 5543475439981447857203897)
        ·
          refine ⟨4157606579986085892902923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5543475439981447857203897 4157606579986085892902923)
          ·
            refine ⟨6236409869979128839354385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4157606579986085892902923 6236409869979128839354385)
            ·
              refine ⟨4677307402484346629515789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6236409869979128839354385 4677307402484346629515789)
              ·
                refine ⟨1753990275931629986068421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4677307402484346629515789 1753990275931629986068421)
                ·
                  refine ⟨328873176737180622387829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1753990275931629986068421 328873176737180622387829)
                  ·
                    rfl

theorem cell22_2882152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 3, 4].length) (baseStart_2882152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2882152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2882152 prefixEnd_2882152 := by exact prefixLift 2882152
  have htrace : WordTrace (prefixWord ++ tailWord_2882152) baseStart_2882152 baseEnd_2882152 := by
    simpa [prefixWord, tailWord_2882152, baseEnd_2882152] using wordTrace_append hprefix tailTrace_2882152
  have hstable : (prefixWord ++ tailWord_2882152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882152).length < 2 ^ (prefixWord ++ tailWord_2882152).sum := by decide
  have hdescent : baseEnd_2882152 < baseStart_2882152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882287 : List Nat := [1, 1, 2, 1, 5, 2, 4, 2, 4]
def baseStart_2882287 : Nat := 118140960795 + 2882287 * 2 ^ 59
def prefixEnd_2882287 : Nat := 4983230072969 + 3 ^ 40 * 2882287 * 2
def baseEnd_2882287 : Nat := 328888581156815505012691

theorem tailTrace_2882287 : CollatzResearch.WordTrace tailWord_2882287 prefixEnd_2882287 328888581156815505012691 := by
  unfold tailWord_2882287
  simp only [CollatzResearch.WordTrace]
  refine ⟨105125643308973929274253115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70083762205982619516168743 105125643308973929274253115)
  ·
    refine ⟨157688464963460893911379673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105125643308973929274253115 157688464963460893911379673)
    ·
      refine ⟨118266348722595670433534755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157688464963460893911379673 118266348722595670433534755)
      ·
        refine ⟨177399523083893505650302133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118266348722595670433534755 177399523083893505650302133)
        ·
          refine ⟨16631205289115016154715825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 177399523083893505650302133 16631205289115016154715825)
          ·
            refine ⟨12473403966836262116036869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16631205289115016154715825 12473403966836262116036869)
            ·
              refine ⟨2338763243781799146756913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12473403966836262116036869 2338763243781799146756913)
              ·
                refine ⟨1754072432836349360067685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2338763243781799146756913 1754072432836349360067685)
                ·
                  refine ⟨328888581156815505012691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1754072432836349360067685 328888581156815505012691)
                  ·
                    rfl

theorem cell22_2882287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 2, 4].length) (baseStart_2882287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2882287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2882287 prefixEnd_2882287 := by exact prefixLift 2882287
  have htrace : WordTrace (prefixWord ++ tailWord_2882287) baseStart_2882287 baseEnd_2882287 := by
    simpa [prefixWord, tailWord_2882287, baseEnd_2882287] using wordTrace_append hprefix tailTrace_2882287
  have hstable : (prefixWord ++ tailWord_2882287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882287).length < 2 ^ (prefixWord ++ tailWord_2882287).sum := by decide
  have hdescent : baseEnd_2882287 < baseStart_2882287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882298 : List Nat := [3, 1, 1, 1, 1, 3, 5, 7]
def baseStart_2882298 : Nat := 118140960795 + 2882298 * 2 ^ 59
def prefixEnd_2882298 : Nat := 4983230072969 + 3 ^ 40 * 2882298 * 2
def baseEnd_2882298 : Nat := 109629945443916239223671

theorem tailTrace_2882298 : CollatzResearch.WordTrace tailWord_2882298 prefixEnd_2882298 109629945443916239223671 := by
  unfold tailWord_2882298
  simp only [CollatzResearch.WordTrace]
  refine ⟨26281511127983519538225887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70084029674622718768602365 26281511127983519538225887)
  ·
    refine ⟨39422266691975279307338831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26281511127983519538225887 39422266691975279307338831)
    ·
      refine ⟨59133400037962918961008247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39422266691975279307338831 59133400037962918961008247)
      ·
        refine ⟨88700100056944378441512371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59133400037962918961008247 88700100056944378441512371)
        ·
          refine ⟨133050150085416567662268557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88700100056944378441512371 133050150085416567662268557)
          ·
            refine ⟨49893806282031212873350709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133050150085416567662268557 49893806282031212873350709)
            ·
              refine ⟨4677544338940426206876629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49893806282031212873350709 4677544338940426206876629)
              ·
                refine ⟨109629945443916239223671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4677544338940426206876629 109629945443916239223671)
                ·
                  rfl

theorem cell22_2882298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 7].length) (baseStart_2882298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2882298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2882298 prefixEnd_2882298 := by exact prefixLift 2882298
  have htrace : WordTrace (prefixWord ++ tailWord_2882298) baseStart_2882298 baseEnd_2882298 := by
    simpa [prefixWord, tailWord_2882298, baseEnd_2882298] using wordTrace_append hprefix tailTrace_2882298
  have hstable : (prefixWord ++ tailWord_2882298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882298).length < 2 ^ (prefixWord ++ tailWord_2882298).sum := by decide
  have hdescent : baseEnd_2882298 < baseStart_2882298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882302 : List Nat := [4, 2, 2, 1, 2, 2, 2, 1, 1, 5]
def baseStart_2882302 : Nat := 118140960795 + 2882302 * 2 ^ 59
def prefixEnd_2882302 : Nat := 4983230072969 + 3 ^ 40 * 2882302 * 2
def baseEnd_2882302 : Nat := 986670878276991475913027

theorem tailTrace_2882302 : CollatzResearch.WordTrace tailWord_2882302 prefixEnd_2882302 986670878276991475913027 := by
  unfold tailWord_2882302
  simp only [CollatzResearch.WordTrace]
  refine ⟨13140773800489948354506145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70084126935946391224032773 13140773800489948354506145)
  ·
    refine ⟨9855580350367461265879609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13140773800489948354506145 9855580350367461265879609)
    ·
      refine ⟨7391685262775595949409707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9855580350367461265879609 7391685262775595949409707)
      ·
        refine ⟨11087527894163393924114561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7391685262775595949409707 11087527894163393924114561)
        ·
          refine ⟨8315645920622545443085921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11087527894163393924114561 8315645920622545443085921)
          ·
            refine ⟨6236734440466909082314441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8315645920622545443085921 6236734440466909082314441)
            ·
              refine ⟨4677550830350181811735831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6236734440466909082314441 4677550830350181811735831)
              ·
                refine ⟨7016326245525272717603747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4677550830350181811735831 7016326245525272717603747)
                ·
                  refine ⟨10524489368287909076405621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7016326245525272717603747 10524489368287909076405621)
                  ·
                    refine ⟨986670878276991475913027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10524489368287909076405621 986670878276991475913027)
                    ·
                      rfl

theorem cell22_2882302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_2882302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2882302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2882302 prefixEnd_2882302 := by exact prefixLift 2882302
  have htrace : WordTrace (prefixWord ++ tailWord_2882302) baseStart_2882302 baseEnd_2882302 := by
    simpa [prefixWord, tailWord_2882302, baseEnd_2882302] using wordTrace_append hprefix tailTrace_2882302
  have hstable : (prefixWord ++ tailWord_2882302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882302).length < 2 ^ (prefixWord ++ tailWord_2882302).sum := by decide
  have hdescent : baseEnd_2882302 < baseStart_2882302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882330 : List Nat := [3, 1, 1, 3, 2, 1, 1, 2, 5, 3]
def baseStart_2882330 : Nat := 118140960795 + 2882330 * 2 ^ 59
def prefixEnd_2882330 : Nat := 4983230072969 + 3 ^ 40 * 2882330 * 2
def baseEnd_2882330 : Nat := 986680463249208736212941

theorem tailTrace_2882330 : CollatzResearch.WordTrace tailWord_2882330 prefixEnd_2882330 986680463249208736212941 := by
  unfold tailWord_2882330
  simp only [CollatzResearch.WordTrace]
  refine ⟨26281802911954536904517111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70084807765212098412045629 26281802911954536904517111)
  ·
    refine ⟨39422704367931805356775667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26281802911954536904517111 39422704367931805356775667)
    ·
      refine ⟨59134056551897708035163501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39422704367931805356775667 59134056551897708035163501)
      ·
        refine ⟨22175271206961640513186313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59134056551897708035163501 22175271206961640513186313)
        ·
          refine ⟨16631453405221230384889735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22175271206961640513186313 16631453405221230384889735)
          ·
            refine ⟨24947180107831845577334603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16631453405221230384889735 24947180107831845577334603)
            ·
              refine ⟨37420770161747768366001905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24947180107831845577334603 37420770161747768366001905)
              ·
                refine ⟨28065577621310826274501429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37420770161747768366001905 28065577621310826274501429)
                ·
                  refine ⟨2631147901997889963234509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28065577621310826274501429 2631147901997889963234509)
                  ·
                    refine ⟨986680463249208736212941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2631147901997889963234509 986680463249208736212941)
                    ·
                      rfl

theorem cell22_2882330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 5, 3].length) (baseStart_2882330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2882330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2882330 prefixEnd_2882330 := by exact prefixLift 2882330
  have htrace : WordTrace (prefixWord ++ tailWord_2882330) baseStart_2882330 baseEnd_2882330 := by
    simpa [prefixWord, tailWord_2882330, baseEnd_2882330] using wordTrace_append hprefix tailTrace_2882330
  have hstable : (prefixWord ++ tailWord_2882330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882330).length < 2 ^ (prefixWord ++ tailWord_2882330).sum := by decide
  have hdescent : baseEnd_2882330 < baseStart_2882330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882405 : List Nat := [1, 3, 1, 3, 1, 1, 5, 1, 6]
def baseStart_2882405 : Nat := 118140960795 + 2882405 * 2 ^ 59
def prefixEnd_2882405 : Nat := 4983230072969 + 3 ^ 40 * 2882405 * 2
def baseEnd_2882405 : Nat := 328902045760644513529237

theorem tailTrace_2882405 : CollatzResearch.WordTrace tailWord_2882405 prefixEnd_2882405 328902045760644513529237 := by
  unfold tailWord_2882405
  simp only [CollatzResearch.WordTrace]
  refine ⟨105129947122546435427048669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70086631415030956951365779 105129947122546435427048669)
  ·
    refine ⟨39423730170954913285143251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105129947122546435427048669 39423730170954913285143251)
    ·
      refine ⟨59135595256432369927714877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39423730170954913285143251 59135595256432369927714877)
      ·
        refine ⟨22175848221162138722893079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59135595256432369927714877 22175848221162138722893079)
        ·
          refine ⟨33263772331743208084339619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22175848221162138722893079 33263772331743208084339619)
          ·
            refine ⟨49895658497614812126509429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33263772331743208084339619 49895658497614812126509429)
            ·
              refine ⟨4677717984151388636860259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49895658497614812126509429 4677717984151388636860259)
              ·
                refine ⟨7016576976227082955290389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4677717984151388636860259 7016576976227082955290389)
                ·
                  refine ⟨328902045760644513529237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7016576976227082955290389 328902045760644513529237)
                  ·
                    rfl

theorem cell22_2882405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 6].length) (baseStart_2882405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2882405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2882405 prefixEnd_2882405 := by exact prefixLift 2882405
  have htrace : WordTrace (prefixWord ++ tailWord_2882405) baseStart_2882405 baseEnd_2882405 := by
    simpa [prefixWord, tailWord_2882405, baseEnd_2882405] using wordTrace_append hprefix tailTrace_2882405
  have hstable : (prefixWord ++ tailWord_2882405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882405).length < 2 ^ (prefixWord ++ tailWord_2882405).sum := by decide
  have hdescent : baseEnd_2882405 < baseStart_2882405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882450 : List Nat := [3, 2, 3, 2, 12]
def baseStart_2882450 : Nat := 118140960795 + 2882450 * 2 ^ 59
def prefixEnd_2882450 : Nat := 4983230072969 + 3 ^ 40 * 2882450 * 2
def baseEnd_2882450 : Nat := 4060582476138141659311

theorem tailTrace_2882450 : CollatzResearch.WordTrace tailWord_2882450 prefixEnd_2882450 4060582476138141659311 := by
  unfold tailWord_2882450
  simp only [CollatzResearch.WordTrace]
  refine ⟨26282897101845852028109201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70087725604922272074957869 26282897101845852028109201)
  ·
    refine ⟨19712172826384389021081901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26282897101845852028109201 19712172826384389021081901)
    ·
      refine ⟨7392064809894145882905713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19712172826384389021081901 7392064809894145882905713)
      ·
        refine ⟨5544048607420609412179285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7392064809894145882905713 5544048607420609412179285)
        ·
          refine ⟨4060582476138141659311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 5544048607420609412179285 4060582476138141659311)
          ·
            rfl

theorem cell22_2882450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 12].length) (baseStart_2882450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2882450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2882450 prefixEnd_2882450 := by exact prefixLift 2882450
  have htrace : WordTrace (prefixWord ++ tailWord_2882450) baseStart_2882450 baseEnd_2882450 := by
    simpa [prefixWord, tailWord_2882450, baseEnd_2882450] using wordTrace_append hprefix tailTrace_2882450
  have hstable : (prefixWord ++ tailWord_2882450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882450).length < 2 ^ (prefixWord ++ tailWord_2882450).sum := by decide
  have hdescent : baseEnd_2882450 < baseStart_2882450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882452 : List Nat := [2, 4, 2, 1, 1, 1, 1, 4, 2, 4]
def baseStart_2882452 : Nat := 118140960795 + 2882452 * 2 ^ 59
def prefixEnd_2882452 : Nat := 4983230072969 + 3 ^ 40 * 2882452 * 2
def baseEnd_2882452 : Nat := 986722226342441084662567

theorem tailTrace_2882452 : CollatzResearch.WordTrace tailWord_2882452 prefixEnd_2882452 986722226342441084662567 := by
  unfold tailWord_2882452
  simp only [CollatzResearch.WordTrace]
  refine ⟨52565830676688081227004805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70087774235584108302673073 52565830676688081227004805)
  ·
    refine ⟨9856093251879015230063401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52565830676688081227004805 9856093251879015230063401)
    ·
      refine ⟨7392069938909261422547551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9856093251879015230063401 7392069938909261422547551)
      ·
        refine ⟨11088104908363892133821327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7392069938909261422547551 11088104908363892133821327)
        ·
          refine ⟨16632157362545838200731991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11088104908363892133821327 16632157362545838200731991)
          ·
            refine ⟨24948236043818757301097987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16632157362545838200731991 24948236043818757301097987)
            ·
              refine ⟨37422354065728135951646981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24948236043818757301097987 37422354065728135951646981)
              ·
                refine ⟨7016691387324025490933809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37422354065728135951646981 7016691387324025490933809)
                ·
                  refine ⟨5262518540493019118200357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7016691387324025490933809 5262518540493019118200357)
                  ·
                    refine ⟨986722226342441084662567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5262518540493019118200357 986722226342441084662567)
                    ·
                      rfl

theorem cell22_2882452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_2882452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2882452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2882452 prefixEnd_2882452 := by exact prefixLift 2882452
  have htrace : WordTrace (prefixWord ++ tailWord_2882452) baseStart_2882452 baseEnd_2882452 := by
    simpa [prefixWord, tailWord_2882452, baseEnd_2882452] using wordTrace_append hprefix tailTrace_2882452
  have hstable : (prefixWord ++ tailWord_2882452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882452).length < 2 ^ (prefixWord ++ tailWord_2882452).sum := by decide
  have hdescent : baseEnd_2882452 < baseStart_2882452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882516 : List Nat := [2, 4, 1, 2, 1, 2, 2, 4, 1, 3]
def baseStart_2882516 : Nat := 118140960795 + 2882516 * 2 ^ 59
def prefixEnd_2882516 : Nat := 4983230072969 + 3 ^ 40 * 2882516 * 2
def baseEnd_2882516 : Nat := 986744134850366251062371

theorem tailTrace_2882516 : CollatzResearch.WordTrace tailWord_2882516 prefixEnd_2882516 986744134850366251062371 := by
  unfold tailWord_2882516
  simp only [CollatzResearch.WordTrace]
  refine ⟨52566997812572150692169701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70089330416762867589559601 52566997812572150692169701)
  ·
    refine ⟨9856312089857278254781819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52566997812572150692169701 9856312089857278254781819)
    ·
      refine ⟨14784468134785917382172729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9856312089857278254781819 14784468134785917382172729)
      ·
        refine ⟨11088351101089438036629547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14784468134785917382172729 11088351101089438036629547)
        ·
          refine ⟨16632526651634157054944321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11088351101089438036629547 16632526651634157054944321)
          ·
            refine ⟨12474394988725617791208241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16632526651634157054944321 12474394988725617791208241)
            ·
              refine ⟨9355796241544213343406181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12474394988725617791208241 9355796241544213343406181)
              ·
                refine ⟨1754211795289540001888659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9355796241544213343406181 1754211795289540001888659)
                ·
                  refine ⟨2631317692934310002832989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1754211795289540001888659 2631317692934310002832989)
                  ·
                    refine ⟨986744134850366251062371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2631317692934310002832989 986744134850366251062371)
                    ·
                      rfl

theorem cell22_2882516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_2882516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2882516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2882516 prefixEnd_2882516 := by exact prefixLift 2882516
  have htrace : WordTrace (prefixWord ++ tailWord_2882516) baseStart_2882516 baseEnd_2882516 := by
    simpa [prefixWord, tailWord_2882516, baseEnd_2882516] using wordTrace_append hprefix tailTrace_2882516
  have hstable : (prefixWord ++ tailWord_2882516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882516).length < 2 ^ (prefixWord ++ tailWord_2882516).sum := by decide
  have hdescent : baseEnd_2882516 < baseStart_2882516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882555 : List Nat := [1, 1, 1, 1, 1, 3, 3, 3, 3, 5]
def baseStart_2882555 : Nat := 118140960795 + 2882555 * 2 ^ 59
def prefixEnd_2882555 : Nat := 4983230072969 + 3 ^ 40 * 2882555 * 2
def baseEnd_2882555 : Nat := 986757485347383149337251

theorem tailTrace_2882555 : CollatzResearch.WordTrace tailWord_2882555 prefixEnd_2882555 986757485347383149337251 := by
  unfold tailWord_2882555
  simp only [CollatzResearch.WordTrace]
  refine ⟨105135418072003011045009119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70090278714668674030006079 105135418072003011045009119)
  ·
    refine ⟨157703127108004516567513679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105135418072003011045009119 157703127108004516567513679)
    ·
      refine ⟨236554690662006774851270519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157703127108004516567513679 236554690662006774851270519)
      ·
        refine ⟨354832035993010162276905779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236554690662006774851270519 354832035993010162276905779)
        ·
          refine ⟨532248053989515243415358669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354832035993010162276905779 532248053989515243415358669)
          ·
            refine ⟨199593020246068216280759501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 532248053989515243415358669 199593020246068216280759501)
            ·
              refine ⟨74847382592275581105284813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199593020246068216280759501 74847382592275581105284813)
              ·
                refine ⟨28067768472103342914481805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74847382592275581105284813 28067768472103342914481805)
                ·
                  refine ⟨10525413177038753592930677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28067768472103342914481805 10525413177038753592930677)
                  ·
                    refine ⟨986757485347383149337251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10525413177038753592930677 986757485347383149337251)
                    ·
                      rfl

theorem cell22_2882555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 5].length) (baseStart_2882555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2882555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2882555 prefixEnd_2882555 := by exact prefixLift 2882555
  have htrace : WordTrace (prefixWord ++ tailWord_2882555) baseStart_2882555 baseEnd_2882555 := by
    simpa [prefixWord, tailWord_2882555, baseEnd_2882555] using wordTrace_append hprefix tailTrace_2882555
  have hstable : (prefixWord ++ tailWord_2882555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882555).length < 2 ^ (prefixWord ++ tailWord_2882555).sum := by decide
  have hdescent : baseEnd_2882555 < baseStart_2882555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882574 : List Nat := [4, 1, 1, 2, 2, 4, 1, 1, 6]
def baseStart_2882574 : Nat := 118140960795 + 2882574 * 2 ^ 59
def prefixEnd_2882574 : Nat := 4983230072969 + 3 ^ 40 * 2882574 * 2
def baseEnd_2882574 : Nat := 328921329811891144370731

theorem tailTrace_2882574 : CollatzResearch.WordTrace tailWord_2882574 prefixEnd_2882574 328921329811891144370731 := by
  unfold tailWord_2882574
  simp only [CollatzResearch.WordTrace]
  refine ⟨13142013882366772161243847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70090740705956118193300517 13142013882366772161243847)
  ·
    refine ⟨19713020823550158241865771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13142013882366772161243847 19713020823550158241865771)
    ·
      refine ⟨29569531235325237362798657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19713020823550158241865771 29569531235325237362798657)
      ·
        refine ⟨22177148426493928022098993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29569531235325237362798657 22177148426493928022098993)
        ·
          refine ⟨16632861319870446016574245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22177148426493928022098993 16632861319870446016574245)
          ·
            refine ⟨3118661497475708628107671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16632861319870446016574245 3118661497475708628107671)
            ·
              refine ⟨4677992246213562942161507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3118661497475708628107671 4677992246213562942161507)
              ·
                refine ⟨7016988369320344413242261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4677992246213562942161507 7016988369320344413242261)
                ·
                  refine ⟨328921329811891144370731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7016988369320344413242261 328921329811891144370731)
                  ·
                    rfl

theorem cell22_2882574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 6].length) (baseStart_2882574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2882574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2882574 prefixEnd_2882574 := by exact prefixLift 2882574
  have htrace : WordTrace (prefixWord ++ tailWord_2882574) baseStart_2882574 baseEnd_2882574 := by
    simpa [prefixWord, tailWord_2882574, baseEnd_2882574] using wordTrace_append hprefix tailTrace_2882574
  have hstable : (prefixWord ++ tailWord_2882574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882574).length < 2 ^ (prefixWord ++ tailWord_2882574).sum := by decide
  have hdescent : baseEnd_2882574 < baseStart_2882574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882585 : List Nat := [1, 2, 1, 2, 1, 1, 5, 9]
def baseStart_2882585 : Nat := 118140960795 + 2882585 * 2 ^ 59
def prefixEnd_2882585 : Nat := 4983230072969 + 3 ^ 40 * 2882585 * 2
def baseEnd_2882585 : Nat := 109640861662274785676351

theorem tailTrace_2882585 : CollatzResearch.WordTrace tailWord_2882585 prefixEnd_2882585 109640861662274785676351 := by
  unfold tailWord_2882585
  simp only [CollatzResearch.WordTrace]
  refine ⟨105136512261894326168601209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70091008174596217445734139 105136512261894326168601209)
  ·
    refine ⟨78852384196420744626450907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105136512261894326168601209 78852384196420744626450907)
    ·
      refine ⟨118278576294631116939676361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78852384196420744626450907 118278576294631116939676361)
      ·
        refine ⟨88708932220973337704757271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118278576294631116939676361 88708932220973337704757271)
        ·
          refine ⟨133063398331460006557135907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88708932220973337704757271 133063398331460006557135907)
          ·
            refine ⟨199595097497190009835703861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133063398331460006557135907 199595097497190009835703861)
            ·
              refine ⟨18712040390361563422097237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 199595097497190009835703861 18712040390361563422097237)
              ·
                refine ⟨109640861662274785676351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18712040390361563422097237 109640861662274785676351)
                ·
                  rfl

theorem cell22_2882585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 9].length) (baseStart_2882585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2882585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2882585 prefixEnd_2882585 := by exact prefixLift 2882585
  have htrace : WordTrace (prefixWord ++ tailWord_2882585) baseStart_2882585 baseEnd_2882585 := by
    simpa [prefixWord, tailWord_2882585, baseEnd_2882585] using wordTrace_append hprefix tailTrace_2882585
  have hstable : (prefixWord ++ tailWord_2882585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882585).length < 2 ^ (prefixWord ++ tailWord_2882585).sum := by decide
  have hdescent : baseEnd_2882585 < baseStart_2882585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882625 : List Nat := [1, 2, 5, 1, 4, 1, 2, 2, 4]
def baseStart_2882625 : Nat := 118140960795 + 2882625 * 2 ^ 59
def prefixEnd_2882625 : Nat := 4983230072969 + 3 ^ 40 * 2882625 * 2
def baseEnd_2882625 : Nat := 328927149259308766695679

theorem tailTrace_2882625 : CollatzResearch.WordTrace tailWord_2882625 prefixEnd_2882625 328927149259308766695679 := by
  unfold tailWord_2882625
  simp only [CollatzResearch.WordTrace]
  refine ⟨105137971181749413000057329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70091980787832942000038219 105137971181749413000057329)
  ·
    refine ⟨78853478386312059750042997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105137971181749413000057329 78853478386312059750042997)
    ·
      refine ⟨7392513598716755601566531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78853478386312059750042997 7392513598716755601566531)
      ·
        refine ⟨11088770398075133402349797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7392513598716755601566531 11088770398075133402349797)
        ·
          refine ⟨2079144449639087512940587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11088770398075133402349797 2079144449639087512940587)
          ·
            refine ⟨3118716674458631269410881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2079144449639087512940587 3118716674458631269410881)
            ·
              refine ⟨2339037505843973452058161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3118716674458631269410881 2339037505843973452058161)
              ·
                refine ⟨1754278129382980089043621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2339037505843973452058161 1754278129382980089043621)
                ·
                  refine ⟨328927149259308766695679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1754278129382980089043621 328927149259308766695679)
                  ·
                    rfl

theorem cell22_2882625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 2, 4].length) (baseStart_2882625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2882625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2882625 prefixEnd_2882625 := by exact prefixLift 2882625
  have htrace : WordTrace (prefixWord ++ tailWord_2882625) baseStart_2882625 baseEnd_2882625 := by
    simpa [prefixWord, tailWord_2882625, baseEnd_2882625] using wordTrace_append hprefix tailTrace_2882625
  have hstable : (prefixWord ++ tailWord_2882625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882625).length < 2 ^ (prefixWord ++ tailWord_2882625).sum := by decide
  have hdescent : baseEnd_2882625 < baseStart_2882625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882681 : List Nat := [1, 2, 1, 3, 5, 2, 1, 2, 5]
def baseStart_2882681 : Nat := 118140960795 + 2882681 * 2 ^ 59
def prefixEnd_2882681 : Nat := 4983230072969 + 3 ^ 40 * 2882681 * 2
def baseEnd_2882681 : Nat := 328933539240786940228955

theorem tailTrace_2882681 : CollatzResearch.WordTrace tailWord_2882681 prefixEnd_2882681 328933539240786940228955 := by
  unfold tailWord_2882681
  simp only [CollatzResearch.WordTrace]
  refine ⟨105140013669546534564095897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70093342446364356376063931 105140013669546534564095897)
  ·
    refine ⟨78855010252159900923071923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105140013669546534564095897 78855010252159900923071923)
    ·
      refine ⟨118282515378239851384607885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78855010252159900923071923 118282515378239851384607885)
      ·
        refine ⟨44355943266839944269227957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118282515378239851384607885 44355943266839944269227957)
        ·
          refine ⟨4158369681266244775240121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44355943266839944269227957 4158369681266244775240121)
          ·
            refine ⟨3118777260949683581430091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4158369681266244775240121 3118777260949683581430091)
            ·
              refine ⟨4678165891424525372145137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3118777260949683581430091 4678165891424525372145137)
              ·
                refine ⟨3508624418568394029108853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4678165891424525372145137 3508624418568394029108853)
                ·
                  refine ⟨328933539240786940228955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3508624418568394029108853 328933539240786940228955)
                  ·
                    rfl

theorem cell22_2882681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 2, 5].length) (baseStart_2882681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2882681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2882681 prefixEnd_2882681 := by exact prefixLift 2882681
  have htrace : WordTrace (prefixWord ++ tailWord_2882681) baseStart_2882681 baseEnd_2882681 := by
    simpa [prefixWord, tailWord_2882681, baseEnd_2882681] using wordTrace_append hprefix tailTrace_2882681
  have hstable : (prefixWord ++ tailWord_2882681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882681).length < 2 ^ (prefixWord ++ tailWord_2882681).sum := by decide
  have hdescent : baseEnd_2882681 < baseStart_2882681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882711 : List Nat := [1, 1, 3, 3, 3, 2, 2, 2, 1, 4]
def baseStart_2882711 : Nat := 118140960795 + 2882711 * 2 ^ 59
def prefixEnd_2882711 : Nat := 4983230072969 + 3 ^ 40 * 2882711 * 2
def baseEnd_2882711 : Nat := 986810887335450742436773

theorem tailTrace_2882711 : CollatzResearch.WordTrace tailWord_2882711 prefixEnd_2882711 986810887335450742436773 := by
  unfold tailWord_2882711
  simp only [CollatzResearch.WordTrace]
  refine ⟨105141107859437849687687987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70094071906291899791791991 105141107859437849687687987)
  ·
    refine ⟨157711661789156774531531981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105141107859437849687687987 157711661789156774531531981)
    ·
      refine ⟨59141873170933790449324493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157711661789156774531531981 59141873170933790449324493)
      ·
        refine ⟨22178202439100171418496685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59141873170933790449324493 22178202439100171418496685)
        ·
          refine ⟨8316825914662564281936257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22178202439100171418496685 8316825914662564281936257)
          ·
            refine ⟨6237619435996923211452193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8316825914662564281936257 6237619435996923211452193)
            ·
              refine ⟨4678214576997692408589145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6237619435996923211452193 4678214576997692408589145)
              ·
                refine ⟨3508660932748269306441859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4678214576997692408589145 3508660932748269306441859)
                ·
                  refine ⟨5262991399122403959662789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3508660932748269306441859 5262991399122403959662789)
                  ·
                    refine ⟨986810887335450742436773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5262991399122403959662789 986810887335450742436773)
                    ·
                      rfl

theorem cell22_2882711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 2, 1, 4].length) (baseStart_2882711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2882711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2882711 prefixEnd_2882711 := by exact prefixLift 2882711
  have htrace : WordTrace (prefixWord ++ tailWord_2882711) baseStart_2882711 baseEnd_2882711 := by
    simpa [prefixWord, tailWord_2882711, baseEnd_2882711] using wordTrace_append hprefix tailTrace_2882711
  have hstable : (prefixWord ++ tailWord_2882711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882711).length < 2 ^ (prefixWord ++ tailWord_2882711).sum := by decide
  have hdescent : baseEnd_2882711 < baseStart_2882711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882767 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 4, 6]
def baseStart_2882767 : Nat := 118140960795 + 2882767 * 2 ^ 59
def prefixEnd_2882767 : Nat := 4983230072969 + 3 ^ 40 * 2882767 * 2
def baseEnd_2882767 : Nat := 986830057279885263036601

theorem tailTrace_2882767 : CollatzResearch.WordTrace tailWord_2882767 prefixEnd_2882767 986830057279885263036601 := by
  unfold tailWord_2882767
  simp only [CollatzResearch.WordTrace]
  refine ⟨105143150347234971251726555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70095433564823314167817703 105143150347234971251726555)
  ·
    refine ⟨157714725520852456877589833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105143150347234971251726555 157714725520852456877589833)
    ·
      refine ⟨118286044140639342658192375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157714725520852456877589833 118286044140639342658192375)
      ·
        refine ⟨177429066210959013987288563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118286044140639342658192375 177429066210959013987288563)
        ·
          refine ⟨266143599316438520980932845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177429066210959013987288563 266143599316438520980932845)
          ·
            refine ⟨99803849743664445367849817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 266143599316438520980932845 99803849743664445367849817)
            ·
              refine ⟨74852887307748334025887363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99803849743664445367849817 74852887307748334025887363)
              ·
                refine ⟨112279330961622501038831045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74852887307748334025887363 112279330961622501038831045)
                ·
                  refine ⟨21052374555304218944780821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112279330961622501038831045 21052374555304218944780821)
                  ·
                    refine ⟨986830057279885263036601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21052374555304218944780821 986830057279885263036601)
                    ·
                      rfl

theorem cell22_2882767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 6].length) (baseStart_2882767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2882767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2882767 prefixEnd_2882767 := by exact prefixLift 2882767
  have htrace : WordTrace (prefixWord ++ tailWord_2882767) baseStart_2882767 baseEnd_2882767 := by
    simpa [prefixWord, tailWord_2882767, baseEnd_2882767] using wordTrace_append hprefix tailTrace_2882767
  have hstable : (prefixWord ++ tailWord_2882767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882767).length < 2 ^ (prefixWord ++ tailWord_2882767).sum := by decide
  have hdescent : baseEnd_2882767 < baseStart_2882767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882769 : List Nat := [1, 2, 2, 1, 2, 2, 1, 3, 5, 3]
def baseStart_2882769 : Nat := 118140960795 + 2882769 * 2 ^ 59
def prefixEnd_2882769 : Nat := 4983230072969 + 3 ^ 40 * 2882769 * 2
def baseEnd_2882769 : Nat := 986830741920757924486595

theorem tailTrace_2882769 : CollatzResearch.WordTrace tailWord_2882769 prefixEnd_2882769 986830741920757924486595 := by
  unfold tailWord_2882769
  simp only [CollatzResearch.WordTrace]
  refine ⟨105143223293227725593299361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70095482195485150395532907 105143223293227725593299361)
  ·
    refine ⟨78857417469920794194974521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105143223293227725593299361 78857417469920794194974521)
    ·
      refine ⟨59143063102440595646230891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78857417469920794194974521 59143063102440595646230891)
      ·
        refine ⟨88714594653660893469346337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59143063102440595646230891 88714594653660893469346337)
        ·
          refine ⟨66535945990245670102009753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88714594653660893469346337 66535945990245670102009753)
          ·
            refine ⟨49901959492684252576507315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66535945990245670102009753 49901959492684252576507315)
            ·
              refine ⟨74852939239026378864760973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49901959492684252576507315 74852939239026378864760973)
              ·
                refine ⟨28069852214634892074285365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74852939239026378864760973 28069852214634892074285365)
                ·
                  refine ⟨2631548645122021131964253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28069852214634892074285365 2631548645122021131964253)
                  ·
                    refine ⟨986830741920757924486595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2631548645122021131964253 986830741920757924486595)
                    ·
                      rfl

theorem cell22_2882769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 5, 3].length) (baseStart_2882769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2882769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2882769 prefixEnd_2882769 := by exact prefixLift 2882769
  have htrace : WordTrace (prefixWord ++ tailWord_2882769) baseStart_2882769 baseEnd_2882769 := by
    simpa [prefixWord, tailWord_2882769, baseEnd_2882769] using wordTrace_append hprefix tailTrace_2882769
  have hstable : (prefixWord ++ tailWord_2882769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882769).length < 2 ^ (prefixWord ++ tailWord_2882769).sum := by decide
  have hdescent : baseEnd_2882769 < baseStart_2882769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882803 : List Nat := [1, 1, 1, 2, 2, 6, 1, 4, 1, 3]
def baseStart_2882803 : Nat := 118140960795 + 2882803 * 2 ^ 59
def prefixEnd_2882803 : Nat := 4983230072969 + 3 ^ 40 * 2882803 * 2
def baseEnd_2882803 : Nat := 986842380815593169136491

theorem tailTrace_2882803 : CollatzResearch.WordTrace tailWord_2882803 prefixEnd_2882803 986842380815593169136491 := by
  unfold tailWord_2882803
  simp only [CollatzResearch.WordTrace]
  refine ⟨105144463375104549400037063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70096308916736366266691375 105144463375104549400037063)
  ·
    refine ⟨157716695062656824100055595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105144463375104549400037063 157716695062656824100055595)
    ·
      refine ⟨236575042593985236150083393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157716695062656824100055595 236575042593985236150083393)
      ·
        refine ⟨177431281945488927112562545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236575042593985236150083393 177431281945488927112562545)
        ·
          refine ⟨133073461459116695334421909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177431281945488927112562545 133073461459116695334421909)
          ·
            refine ⟨6237818505896095093801027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 133073461459116695334421909 6237818505896095093801027)
            ·
              refine ⟨9356727758844142640701541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6237818505896095093801027 9356727758844142640701541)
              ·
                refine ⟨1754386454783276745131539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9356727758844142640701541 1754386454783276745131539)
                ·
                  refine ⟨2631579682174915117697309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1754386454783276745131539 2631579682174915117697309)
                  ·
                    refine ⟨986842380815593169136491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2631579682174915117697309 986842380815593169136491)
                    ·
                      rfl

theorem cell22_2882803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 4, 1, 3].length) (baseStart_2882803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2882803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2882803 prefixEnd_2882803 := by exact prefixLift 2882803
  have htrace : WordTrace (prefixWord ++ tailWord_2882803) baseStart_2882803 baseEnd_2882803 := by
    simpa [prefixWord, tailWord_2882803, baseEnd_2882803] using wordTrace_append hprefix tailTrace_2882803
  have hstable : (prefixWord ++ tailWord_2882803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882803).length < 2 ^ (prefixWord ++ tailWord_2882803).sum := by decide
  have hdescent : baseEnd_2882803 < baseStart_2882803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882850 : List Nat := [3, 3, 1, 1, 5, 1, 1, 2, 5]
def baseStart_2882850 : Nat := 118140960795 + 2882850 * 2 ^ 59
def prefixEnd_2882850 : Nat := 4983230072969 + 3 ^ 40 * 2882850 * 2
def baseEnd_2882850 : Nat := 328952823292033571070449

theorem tailTrace_2882850 : CollatzResearch.WordTrace tailWord_2882850 prefixEnd_2882850 328952823292033571070449 := by
  unfold tailWord_2882850
  simp only [CollatzResearch.WordTrace]
  refine ⟨26286544401483569106749501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70097451737289517617998669 26286544401483569106749501)
  ·
    refine ⟨9857454150556338415031063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26286544401483569106749501 9857454150556338415031063)
    ·
      refine ⟨14786181225834507622546595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9857454150556338415031063 14786181225834507622546595)
      ·
        refine ⟨22179271838751761433819893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14786181225834507622546595 22179271838751761433819893)
        ·
          refine ⟨2079306734882977634420615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22179271838751761433819893 2079306734882977634420615)
          ·
            refine ⟨3118960102324466451630923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2079306734882977634420615 3118960102324466451630923)
            ·
              refine ⟨4678440153486699677446385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3118960102324466451630923 4678440153486699677446385)
              ·
                refine ⟨3508830115115024758084789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4678440153486699677446385 3508830115115024758084789)
                ·
                  refine ⟨328952823292033571070449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3508830115115024758084789 328952823292033571070449)
                  ·
                    rfl

theorem cell22_2882850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_2882850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2882850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2882850 prefixEnd_2882850 := by exact prefixLift 2882850
  have htrace : WordTrace (prefixWord ++ tailWord_2882850) baseStart_2882850 baseEnd_2882850 := by
    simpa [prefixWord, tailWord_2882850, baseEnd_2882850] using wordTrace_append hprefix tailTrace_2882850
  have hstable : (prefixWord ++ tailWord_2882850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882850).length < 2 ^ (prefixWord ++ tailWord_2882850).sum := by decide
  have hdescent : baseEnd_2882850 < baseStart_2882850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882874 : List Nat := [3, 1, 1, 1, 4, 1, 1, 1, 3, 6]
def baseStart_2882874 : Nat := 118140960795 + 2882874 * 2 ^ 59
def prefixEnd_2882874 : Nat := 4983230072969 + 3 ^ 40 * 2882874 * 2
def baseEnd_2882874 : Nat := 986866685566572650611273

theorem tailTrace_2882874 : CollatzResearch.WordTrace tailWord_2882874 prefixEnd_2882874 986866685566572650611273 := by
  unfold tailWord_2882874
  simp only [CollatzResearch.WordTrace]
  refine ⟨26286763239461832131467919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70098035305231552350581117 26286763239461832131467919)
  ·
    refine ⟨39430144859192748197201879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26286763239461832131467919 39430144859192748197201879)
    ·
      refine ⟨59145217288789122295802819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39430144859192748197201879 59145217288789122295802819)
      ·
        refine ⟨88717825933183683443704229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59145217288789122295802819 88717825933183683443704229)
        ·
          refine ⟨16634592362471940645694543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88717825933183683443704229 16634592362471940645694543)
          ·
            refine ⟨24951888543707910968541815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16634592362471940645694543 24951888543707910968541815)
            ·
              refine ⟨37427832815561866452812723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24951888543707910968541815 37427832815561866452812723)
              ·
                refine ⟨56141749223342799679219085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37427832815561866452812723 56141749223342799679219085)
                ·
                  refine ⟨21053155958753549879707157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56141749223342799679219085 21053155958753549879707157)
                  ·
                    refine ⟨986866685566572650611273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21053155958753549879707157 986866685566572650611273)
                    ·
                      rfl

theorem cell22_2882874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 3, 6].length) (baseStart_2882874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2882874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2882874 prefixEnd_2882874 := by exact prefixLift 2882874
  have htrace : WordTrace (prefixWord ++ tailWord_2882874) baseStart_2882874 baseEnd_2882874 := by
    simpa [prefixWord, tailWord_2882874, baseEnd_2882874] using wordTrace_append hprefix tailTrace_2882874
  have hstable : (prefixWord ++ tailWord_2882874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882874).length < 2 ^ (prefixWord ++ tailWord_2882874).sum := by decide
  have hdescent : baseEnd_2882874 < baseStart_2882874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882876 : List Nat := [2, 2, 2, 2, 1, 3, 3, 1, 1, 5]
def baseStart_2882876 : Nat := 118140960795 + 2882876 * 2 ^ 59
def prefixEnd_2882876 : Nat := 4983230072969 + 3 ^ 40 * 2882876 * 2
def baseEnd_2882876 : Nat := 986867370207445312061267

theorem tailTrace_2882876 : CollatzResearch.WordTrace tailWord_2882876 prefixEnd_2882876 986867370207445312061267 := by
  unfold tailWord_2882876
  simp only [CollatzResearch.WordTrace]
  refine ⟨52573562951920041433722241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70098083935893388578296321 52573562951920041433722241)
  ·
    refine ⟨39430172213940031075291681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52573562951920041433722241 39430172213940031075291681)
    ·
      refine ⟨29572629160455023306468761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39430172213940031075291681 29572629160455023306468761)
      ·
        refine ⟨22179471870341267479851571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29572629160455023306468761 22179471870341267479851571)
        ·
          refine ⟨33269207805511901219777357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22179471870341267479851571 33269207805511901219777357)
          ·
            refine ⟨12475952927066962957416509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33269207805511901219777357 12475952927066962957416509)
            ·
              refine ⟨4678482347650111109031191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12475952927066962957416509 4678482347650111109031191)
              ·
                refine ⟨7017723521475166663546787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4678482347650111109031191 7017723521475166663546787)
                ·
                  refine ⟨10526585282212749995320181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7017723521475166663546787 10526585282212749995320181)
                  ·
                    refine ⟨986867370207445312061267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10526585282212749995320181 986867370207445312061267)
                    ·
                      rfl

theorem cell22_2882876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_2882876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2882876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2882876 prefixEnd_2882876 := by exact prefixLift 2882876
  have htrace : WordTrace (prefixWord ++ tailWord_2882876) baseStart_2882876 baseEnd_2882876 := by
    simpa [prefixWord, tailWord_2882876, baseEnd_2882876] using wordTrace_append hprefix tailTrace_2882876
  have hstable : (prefixWord ++ tailWord_2882876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882876).length < 2 ^ (prefixWord ++ tailWord_2882876).sum := by decide
  have hdescent : baseEnd_2882876 < baseStart_2882876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882921 : List Nat := [1, 2, 1, 1, 1, 3, 2, 5, 3, 3]
def baseStart_2882921 : Nat := 118140960795 + 2882921 * 2 ^ 59
def prefixEnd_2882921 : Nat := 4983230072969 + 3 ^ 40 * 2882921 * 2
def baseEnd_2882921 : Nat := 986882774627080194686129

theorem tailTrace_2882921 : CollatzResearch.WordTrace tailWord_2882921 prefixEnd_2882921 986882774627080194686129 := by
  unfold tailWord_2882921
  simp only [CollatzResearch.WordTrace]
  refine ⟨105148767188677055552832617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70099178125784703701888411 105148767188677055552832617)
  ·
    refine ⟨78861575391507791664624463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105148767188677055552832617 78861575391507791664624463)
    ·
      refine ⟨118292363087261687496936695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78861575391507791664624463 118292363087261687496936695)
      ·
        refine ⟨177438544630892531245405043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118292363087261687496936695 177438544630892531245405043)
        ·
          refine ⟨266157816946338796868107565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177438544630892531245405043 266157816946338796868107565)
          ·
            refine ⟨99809181354877048825540337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 266157816946338796868107565 99809181354877048825540337)
            ·
              refine ⟨74856886016157786619155253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99809181354877048825540337 74856886016157786619155253)
              ·
                refine ⟨7017833064014792495545805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74856886016157786619155253 7017833064014792495545805)
                ·
                  refine ⟨2631687399005547185829677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7017833064014792495545805 2631687399005547185829677)
                  ·
                    refine ⟨986882774627080194686129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2631687399005547185829677 986882774627080194686129)
                    ·
                      rfl

theorem cell22_2882921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 3, 3].length) (baseStart_2882921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2882921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2882921 prefixEnd_2882921 := by exact prefixLift 2882921
  have htrace : WordTrace (prefixWord ++ tailWord_2882921) baseStart_2882921 baseEnd_2882921 := by
    simpa [prefixWord, tailWord_2882921, baseEnd_2882921] using wordTrace_append hprefix tailTrace_2882921
  have hstable : (prefixWord ++ tailWord_2882921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882921).length < 2 ^ (prefixWord ++ tailWord_2882921).sum := by decide
  have hdescent : baseEnd_2882921 < baseStart_2882921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2882942 : List Nat := [4, 2, 3, 2, 1, 1, 2, 1, 2, 4]
def baseStart_2882942 : Nat := 118140960795 + 2882942 * 2 ^ 59
def prefixEnd_2882942 : Nat := 4983230072969 + 3 ^ 40 * 2882942 * 2
def baseEnd_2882942 : Nat := 986889963356243139911065

theorem tailTrace_2882942 : CollatzResearch.WordTrace tailWord_2882942 prefixEnd_2882942 986889963356243139911065 := by
  unfold tailWord_2882942
  simp only [CollatzResearch.WordTrace]
  refine ⟨13143691640200122017418385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70099688747733984092898053 13143691640200122017418385)
  ·
    refine ⟨9857768730150091513063789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13143691640200122017418385 9857768730150091513063789)
    ·
      refine ⟨3696663273806284317398921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9857768730150091513063789 3696663273806284317398921)
      ·
        refine ⟨2772497455354713238049191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3696663273806284317398921 2772497455354713238049191)
        ·
          refine ⟨4158746183032069857073787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2772497455354713238049191 4158746183032069857073787)
          ·
            refine ⟨6238119274548104785610681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4158746183032069857073787 6238119274548104785610681)
            ·
              refine ⟨4678589455911078589208011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6238119274548104785610681 4678589455911078589208011)
              ·
                refine ⟨7017884183866617883812017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4678589455911078589208011 7017884183866617883812017)
                ·
                  refine ⟨5263413137899963412859013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7017884183866617883812017 5263413137899963412859013)
                  ·
                    refine ⟨986889963356243139911065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5263413137899963412859013 986889963356243139911065)
                    ·
                      rfl

theorem cell22_2882942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_2882942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2882942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2882942 prefixEnd_2882942 := by exact prefixLift 2882942
  have htrace : WordTrace (prefixWord ++ tailWord_2882942) baseStart_2882942 baseEnd_2882942 := by
    simpa [prefixWord, tailWord_2882942, baseEnd_2882942] using wordTrace_append hprefix tailTrace_2882942
  have hstable : (prefixWord ++ tailWord_2882942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2882942).length < 2 ^ (prefixWord ++ tailWord_2882942).sum := by decide
  have hdescent : baseEnd_2882942 < baseStart_2882942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2882942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883011 : List Nat := [1, 1, 1, 3, 1, 1, 6, 2, 1, 5]
def baseStart_2883011 : Nat := 118140960795 + 2883011 * 2 ^ 59
def prefixEnd_2883011 : Nat := 4983230072969 + 3 ^ 40 * 2883011 * 2
def baseEnd_2883011 : Nat := 986913583466349959935853

theorem tailTrace_2883011 : CollatzResearch.WordTrace tailWord_2883011 prefixEnd_2883011 986913583466349959935853 := by
  unfold tailWord_2883011
  simp only [CollatzResearch.WordTrace]
  refine ⟨105152049758351000923608887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70101366505567333949072591 105152049758351000923608887)
  ·
    refine ⟨157728074637526501385413331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105152049758351000923608887 157728074637526501385413331)
    ·
      refine ⟨236592111956289752078119997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157728074637526501385413331 236592111956289752078119997)
      ·
        refine ⟨88722041983608657029294999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236592111956289752078119997 88722041983608657029294999)
        ·
          refine ⟨133083062975412985543942499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88722041983608657029294999 133083062975412985543942499)
          ·
            refine ⟨199624594463119478315913749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133083062975412985543942499 199624594463119478315913749)
            ·
              refine ⟨9357402865458725546058457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 199624594463119478315913749 9357402865458725546058457)
              ·
                refine ⟨7018052149094044159543843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9357402865458725546058457 7018052149094044159543843)
                ·
                  refine ⟨10527078223641066239315765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7018052149094044159543843 10527078223641066239315765)
                  ·
                    refine ⟨986913583466349959935853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10527078223641066239315765 986913583466349959935853)
                    ·
                      rfl

theorem cell22_2883011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 5].length) (baseStart_2883011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2883011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2883011 prefixEnd_2883011 := by exact prefixLift 2883011
  have htrace : WordTrace (prefixWord ++ tailWord_2883011) baseStart_2883011 baseEnd_2883011 := by
    simpa [prefixWord, tailWord_2883011, baseEnd_2883011] using wordTrace_append hprefix tailTrace_2883011
  have hstable : (prefixWord ++ tailWord_2883011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883011).length < 2 ^ (prefixWord ++ tailWord_2883011).sum := by decide
  have hdescent : baseEnd_2883011 < baseStart_2883011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
