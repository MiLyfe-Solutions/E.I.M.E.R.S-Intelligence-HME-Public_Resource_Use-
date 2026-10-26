import V185TrunkScan23Chunk0373

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2211025 : List Nat := [1, 2, 2, 1, 2, 2, 1, 3, 1, 6, 2]
def baseStart_2211025 : Nat := 118140960795 + 2211025 * 2 ^ 59
def prefixEnd_2211025 : Nat := 4983230072969 + 3 ^ 40 * 2211025 * 2
def baseEnd_2211025 : Nat := 1135318564107317088219187

theorem tailTrace_2211025 : CollatzResearch.WordTrace tailWord_2211025 prefixEnd_2211025 1135318564107317088219187 := by
  unfold tailWord_2211025
  simp only [CollatzResearch.WordTrace]
  refine ⟨80642706814841512851802529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53761804543227675234535019 80642706814841512851802529)
  ·
    refine ⟨60482030111131134638851897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80642706814841512851802529 60482030111131134638851897)
    ·
      refine ⟨45361522583348350979138923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60482030111131134638851897 45361522583348350979138923)
      ·
        refine ⟨68042283875022526468708385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45361522583348350979138923 68042283875022526468708385)
        ·
          refine ⟨51031712906266894851531289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68042283875022526468708385 51031712906266894851531289)
          ·
            refine ⟨38273784679700171138648467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51031712906266894851531289 38273784679700171138648467)
            ·
              refine ⟨57410677019550256707972701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38273784679700171138648467 57410677019550256707972701)
              ·
                refine ⟨21529003882331346265489763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57410677019550256707972701 21529003882331346265489763)
                ·
                  refine ⟨32293505823497019398234645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21529003882331346265489763 32293505823497019398234645)
                  ·
                    refine ⟨1513758085476422784292249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 32293505823497019398234645 1513758085476422784292249)
                    ·
                      refine ⟨1135318564107317088219187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1513758085476422784292249 1135318564107317088219187)
                      ·
                        rfl

theorem cell23_2211025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 6, 2].length) (baseStart_2211025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2211025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2211025 prefixEnd_2211025 := by exact prefixLift 2211025
  have htrace : WordTrace (prefixWord ++ tailWord_2211025) baseStart_2211025 baseEnd_2211025 := by
    simpa [prefixWord, tailWord_2211025, baseEnd_2211025] using wordTrace_append hprefix tailTrace_2211025
  have hstable : (prefixWord ++ tailWord_2211025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211025).length < 2 ^ (prefixWord ++ tailWord_2211025).sum := by decide
  have hdescent : baseEnd_2211025 < baseStart_2211025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211060 : List Nat := [2, 6, 1, 2, 1, 2, 2, 2, 5]
def baseStart_2211060 : Nat := 118140960795 + 2211060 * 2 ^ 59
def prefixEnd_2211060 : Nat := 4983230072969 + 3 ^ 40 * 2211060 * 2
def baseEnd_2211060 : Nat := 126148503992247161253503

theorem tailTrace_2211060 : CollatzResearch.WordTrace tailWord_2211060 prefixEnd_2211060 126148503992247161253503 := by
  unfold tailWord_2211060
  simp only [CollatzResearch.WordTrace]
  refine ⟨40321991684857356914663317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53762655579809809219551089 40321991684857356914663317)
  ·
    refine ⟨1890093360227688605374843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 40321991684857356914663317 1890093360227688605374843)
    ·
      refine ⟨2835140040341532908062265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1890093360227688605374843 2835140040341532908062265)
      ·
        refine ⟨2126355030256149681046699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2835140040341532908062265 2126355030256149681046699)
        ·
          refine ⟨3189532545384224521570049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2126355030256149681046699 3189532545384224521570049)
          ·
            refine ⟨2392149409038168391177537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3189532545384224521570049 2392149409038168391177537)
            ·
              refine ⟨1794112056778626293383153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2392149409038168391177537 1794112056778626293383153)
              ·
                refine ⟨1345584042583969720037365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1794112056778626293383153 1345584042583969720037365)
                ·
                  refine ⟨126148503992247161253503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1345584042583969720037365 126148503992247161253503)
                  ·
                    rfl

theorem cell23_2211060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_2211060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2211060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2211060 prefixEnd_2211060 := by exact prefixLift 2211060
  have htrace : WordTrace (prefixWord ++ tailWord_2211060) baseStart_2211060 baseEnd_2211060 := by
    simpa [prefixWord, tailWord_2211060, baseEnd_2211060] using wordTrace_append hprefix tailTrace_2211060
  have hstable : (prefixWord ++ tailWord_2211060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211060).length < 2 ^ (prefixWord ++ tailWord_2211060).sum := by decide
  have hdescent : baseEnd_2211060 < baseStart_2211060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211065 : List Nat := [1, 2, 1, 3, 1, 1, 6, 2, 6]
def baseStart_2211065 : Nat := 118140960795 + 2211065 * 2 ^ 59
def prefixEnd_2211065 : Nat := 4983230072969 + 3 ^ 40 * 2211065 * 2
def baseEnd_2211065 : Nat := 126148789259277436857667

theorem tailTrace_2211065 : CollatzResearch.WordTrace tailWord_2211065 prefixEnd_2211065 126148789259277436857667 := by
  unfold tailWord_2211065
  simp only [CollatzResearch.WordTrace]
  refine ⟨80644165734696599683258649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53762777156464399788839099 80644165734696599683258649)
  ·
    refine ⟨60483124301022449762443987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80644165734696599683258649 60483124301022449762443987)
    ·
      refine ⟨90724686451533674643665981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60483124301022449762443987 90724686451533674643665981)
      ·
        refine ⟨34021757419325127991374743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90724686451533674643665981 34021757419325127991374743)
        ·
          refine ⟨51032636128987691987062115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34021757419325127991374743 51032636128987691987062115)
          ·
            refine ⟨76548954193481537980593173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51032636128987691987062115 76548954193481537980593173)
            ·
              refine ⟨3588232227819447092840305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 76548954193481537980593173 3588232227819447092840305)
              ·
                refine ⟨2691174170864585319630229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3588232227819447092840305 2691174170864585319630229)
                ·
                  refine ⟨126148789259277436857667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2691174170864585319630229 126148789259277436857667)
                  ·
                    rfl

theorem cell23_2211065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 2, 6].length) (baseStart_2211065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2211065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2211065 prefixEnd_2211065 := by exact prefixLift 2211065
  have htrace : WordTrace (prefixWord ++ tailWord_2211065) baseStart_2211065 baseEnd_2211065 := by
    simpa [prefixWord, tailWord_2211065, baseEnd_2211065] using wordTrace_append hprefix tailTrace_2211065
  have hstable : (prefixWord ++ tailWord_2211065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211065).length < 2 ^ (prefixWord ++ tailWord_2211065).sum := by decide
  have hdescent : baseEnd_2211065 < baseStart_2211065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211088 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 5]
def baseStart_2211088 : Nat := 118140960795 + 2211088 * 2 ^ 59
def prefixEnd_2211088 : Nat := 4983230072969 + 3 ^ 40 * 2211088 * 2
def baseEnd_2211088 : Nat := 1135350913388550341731397

theorem tailTrace_2211088 : CollatzResearch.WordTrace tailWord_2211088 prefixEnd_2211088 1135350913388550341731397 := by
  unfold tailWord_2211088
  simp only [CollatzResearch.WordTrace]
  refine ⟨40322502306806637305672959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53763336409075516407563945 40322502306806637305672959)
  ·
    refine ⟨60483753460209955958509439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40322502306806637305672959 60483753460209955958509439)
    ·
      refine ⟨90725630190314933937764159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60483753460209955958509439 90725630190314933937764159)
      ·
        refine ⟨136088445285472400906646239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90725630190314933937764159 136088445285472400906646239)
        ·
          refine ⟨204132667928208601359969359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136088445285472400906646239 204132667928208601359969359)
          ·
            refine ⟨306199001892312902039954039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204132667928208601359969359 306199001892312902039954039)
            ·
              refine ⟨459298502838469353059931059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 306199001892312902039954039 459298502838469353059931059)
              ·
                refine ⟨688947754257704029589896589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 459298502838469353059931059 688947754257704029589896589)
                ·
                  refine ⟨258355407846639011096211221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 688947754257704029589896589 258355407846639011096211221)
                  ·
                    refine ⟨12110409742811203645134901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 258355407846639011096211221 12110409742811203645134901)
                    ·
                      refine ⟨1135350913388550341731397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12110409742811203645134901 1135350913388550341731397)
                      ·
                        rfl

theorem cell23_2211088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 5].length) (baseStart_2211088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2211088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2211088 prefixEnd_2211088 := by exact prefixLift 2211088
  have htrace : WordTrace (prefixWord ++ tailWord_2211088) baseStart_2211088 baseEnd_2211088 := by
    simpa [prefixWord, tailWord_2211088, baseEnd_2211088] using wordTrace_append hprefix tailTrace_2211088
  have hstable : (prefixWord ++ tailWord_2211088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211088).length < 2 ^ (prefixWord ++ tailWord_2211088).sum := by decide
  have hdescent : baseEnd_2211088 < baseStart_2211088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211095 : List Nat := [1, 1, 3, 4, 1, 1, 1, 3, 3, 5]
def baseStart_2211095 : Nat := 118140960795 + 2211095 * 2 ^ 59
def prefixEnd_2211095 : Nat := 4983230072969 + 3 ^ 40 * 2211095 * 2
def baseEnd_2211095 : Nat := 378451502584377271447955

theorem tailTrace_2211095 : CollatzResearch.WordTrace tailWord_2211095 prefixEnd_2211095 378451502584377271447955 := by
  unfold tailWord_2211095
  simp only [CollatzResearch.WordTrace]
  refine ⟨80645259924587914806850739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53763506616391943204567159 80645259924587914806850739)
  ·
    refine ⟨120967889886881872210276109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80645259924587914806850739 120967889886881872210276109)
    ·
      refine ⟨45362958707580702078853541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120967889886881872210276109 45362958707580702078853541)
      ·
        refine ⟨8505554757671381639785039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45362958707580702078853541 8505554757671381639785039)
        ·
          refine ⟨12758332136507072459677559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8505554757671381639785039 12758332136507072459677559)
          ·
            refine ⟨19137498204760608689516339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12758332136507072459677559 19137498204760608689516339)
            ·
              refine ⟨28706247307140913034274509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19137498204760608689516339 28706247307140913034274509)
              ·
                refine ⟨10764842740177842387852941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28706247307140913034274509 10764842740177842387852941)
                ·
                  refine ⟨4036816027566690895444853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10764842740177842387852941 4036816027566690895444853)
                  ·
                    refine ⟨378451502584377271447955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4036816027566690895444853 378451502584377271447955)
                    ·
                      rfl

theorem cell23_2211095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 3, 5].length) (baseStart_2211095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2211095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2211095 prefixEnd_2211095 := by exact prefixLift 2211095
  have htrace : WordTrace (prefixWord ++ tailWord_2211095) baseStart_2211095 baseEnd_2211095 := by
    simpa [prefixWord, tailWord_2211095, baseEnd_2211095] using wordTrace_append hprefix tailTrace_2211095
  have hstable : (prefixWord ++ tailWord_2211095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211095).length < 2 ^ (prefixWord ++ tailWord_2211095).sum := by decide
  have hdescent : baseEnd_2211095 < baseStart_2211095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211135 : List Nat := [1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 5]
def baseStart_2211135 : Nat := 118140960795 + 2211135 * 2 ^ 59
def prefixEnd_2211135 : Nat := 4983230072969 + 3 ^ 40 * 2211135 * 2
def baseEnd_2211135 : Nat := 1135375046979311657843681

theorem tailTrace_2211135 : CollatzResearch.WordTrace tailWord_2211135 prefixEnd_2211135 1135375046979311657843681 := by
  unfold tailWord_2211135
  simp only [CollatzResearch.WordTrace]
  refine ⟨80646718844443001638306859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53764479229628667758871239 80646718844443001638306859)
  ·
    refine ⟨120970078266664502457460289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80646718844443001638306859 120970078266664502457460289)
    ·
      refine ⟨90727558699998376843095217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120970078266664502457460289 90727558699998376843095217)
      ·
        refine ⟨68045669024998782632321413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90727558699998376843095217 68045669024998782632321413)
        ·
          refine ⟨12758562942187271743560265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68045669024998782632321413 12758562942187271743560265)
          ·
            refine ⟨9568922206640453807670199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12758562942187271743560265 9568922206640453807670199)
            ·
              refine ⟨14353383309960680711505299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9568922206640453807670199 14353383309960680711505299)
              ·
                refine ⟨21530074964941021067257949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14353383309960680711505299 21530074964941021067257949)
                ·
                  refine ⟨8073778111852882900221731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21530074964941021067257949 8073778111852882900221731)
                  ·
                    refine ⟨12110667167779324350332597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8073778111852882900221731 12110667167779324350332597)
                    ·
                      refine ⟨1135375046979311657843681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12110667167779324350332597 1135375046979311657843681)
                      ·
                        rfl

theorem cell23_2211135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 5].length) (baseStart_2211135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2211135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2211135 prefixEnd_2211135 := by exact prefixLift 2211135
  have htrace : WordTrace (prefixWord ++ tailWord_2211135) baseStart_2211135 baseEnd_2211135 := by
    simpa [prefixWord, tailWord_2211135, baseEnd_2211135] using wordTrace_append hprefix tailTrace_2211135
  have hstable : (prefixWord ++ tailWord_2211135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211135).length < 2 ^ (prefixWord ++ tailWord_2211135).sum := by decide
  have hdescent : baseEnd_2211135 < baseStart_2211135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211183 : List Nat := [1, 1, 2, 1, 3, 1, 7, 2, 1, 2, 2]
def baseStart_2211183 : Nat := 118140960795 + 2211183 * 2 ^ 59
def prefixEnd_2211183 : Nat := 4983230072969 + 3 ^ 40 * 2211183 * 2
def baseEnd_2211183 : Nat := 1135399694050727470043461

theorem tailTrace_2211183 : CollatzResearch.WordTrace tailWord_2211183 prefixEnd_2211183 1135399694050727470043461 := by
  unfold tailWord_2211183
  simp only [CollatzResearch.WordTrace]
  refine ⟨80648469548269105836054203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53765646365512737224036135 80648469548269105836054203)
  ·
    refine ⟨120972704322403658754081305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80648469548269105836054203 120972704322403658754081305)
    ·
      refine ⟨90729528241802744065560979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120972704322403658754081305 90729528241802744065560979)
      ·
        refine ⟨136094292362704116098341469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90729528241802744065560979 136094292362704116098341469)
        ·
          refine ⟨51035359636014043536878051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136094292362704116098341469 51035359636014043536878051)
          ·
            refine ⟨76553039454021065305317077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51035359636014043536878051 76553039454021065305317077)
            ·
              refine ⟨1794211862203618718093369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 76553039454021065305317077 1794211862203618718093369)
              ·
                refine ⟨1345658896652714038570027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1794211862203618718093369 1345658896652714038570027)
                ·
                  refine ⟨2018488344979071057855041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1345658896652714038570027 2018488344979071057855041)
                  ·
                    refine ⟨1513866258734303293391281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2018488344979071057855041 1513866258734303293391281)
                    ·
                      refine ⟨1135399694050727470043461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1513866258734303293391281 1135399694050727470043461)
                      ·
                        rfl

theorem cell23_2211183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 2, 1, 2, 2].length) (baseStart_2211183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2211183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2211183 prefixEnd_2211183 := by exact prefixLift 2211183
  have htrace : WordTrace (prefixWord ++ tailWord_2211183) baseStart_2211183 baseEnd_2211183 := by
    simpa [prefixWord, tailWord_2211183, baseEnd_2211183] using wordTrace_append hprefix tailTrace_2211183
  have hstable : (prefixWord ++ tailWord_2211183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211183).length < 2 ^ (prefixWord ++ tailWord_2211183).sum := by decide
  have hdescent : baseEnd_2211183 < baseStart_2211183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211239 : List Nat := [1, 1, 6, 1, 1, 1, 1, 2, 3, 4, 2]
def baseStart_2211239 : Nat := 118140960795 + 2211239 * 2 ^ 59
def prefixEnd_2211239 : Nat := 4983230072969 + 3 ^ 40 * 2211239 * 2
def baseEnd_2211239 : Nat := 1135428448967379250943203

theorem tailTrace_2211239 : CollatzResearch.WordTrace tailWord_2211239 prefixEnd_2211239 1135428448967379250943203 := by
  unfold tailWord_2211239
  simp only [CollatzResearch.WordTrace]
  refine ⟨80650512036066227400092771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53767008024044151600061847 80650512036066227400092771)
  ·
    refine ⟨120975768054099341100139157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80650512036066227400092771 120975768054099341100139157)
    ·
      refine ⟨5670739127535906614069023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 120975768054099341100139157 5670739127535906614069023)
      ·
        refine ⟨8506108691303859921103535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5670739127535906614069023 8506108691303859921103535)
        ·
          refine ⟨12759163036955789881655303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8506108691303859921103535 12759163036955789881655303)
          ·
            refine ⟨19138744555433684822482955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12759163036955789881655303 19138744555433684822482955)
            ·
              refine ⟨28708116833150527233724433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19138744555433684822482955 28708116833150527233724433)
              ·
                refine ⟨21531087624862895425293325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28708116833150527233724433 21531087624862895425293325)
                ·
                  refine ⟨8074157859323585784484997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21531087624862895425293325 8074157859323585784484997)
                  ·
                    refine ⟨1513904598623172334590937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8074157859323585784484997 1513904598623172334590937)
                    ·
                      refine ⟨1135428448967379250943203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1513904598623172334590937 1135428448967379250943203)
                      ·
                        rfl

theorem cell23_2211239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_2211239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2211239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2211239 prefixEnd_2211239 := by exact prefixLift 2211239
  have htrace : WordTrace (prefixWord ++ tailWord_2211239) baseStart_2211239 baseEnd_2211239 := by
    simpa [prefixWord, tailWord_2211239, baseEnd_2211239] using wordTrace_append hprefix tailTrace_2211239
  have hstable : (prefixWord ++ tailWord_2211239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211239).length < 2 ^ (prefixWord ++ tailWord_2211239).sum := by decide
  have hdescent : baseEnd_2211239 < baseStart_2211239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211256 : List Nat := [2, 1, 2, 1, 2, 2, 4, 3, 2, 2, 2]
def baseStart_2211256 : Nat := 118140960795 + 2211256 * 2 ^ 59
def prefixEnd_2211256 : Nat := 4983230072969 + 3 ^ 40 * 2211256 * 2
def baseEnd_2211256 : Nat := 1135437178138505684430625

theorem tailTrace_2211256 : CollatzResearch.WordTrace tailWord_2211256 prefixEnd_2211256 1135437178138505684430625 := by
  unfold tailWord_2211256
  simp only [CollatzResearch.WordTrace]
  refine ⟨40325566038502319651730811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53767421384669759535641081 40325566038502319651730811)
  ·
    refine ⟨60488349057753479477596217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40325566038502319651730811 60488349057753479477596217)
    ·
      refine ⟨45366261793315109608197163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60488349057753479477596217 45366261793315109608197163)
      ·
        refine ⟨68049392689972664412295745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45366261793315109608197163 68049392689972664412295745)
        ·
          refine ⟨51037044517479498309221809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68049392689972664412295745 51037044517479498309221809)
          ·
            refine ⟨38277783388109623731916357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51037044517479498309221809 38277783388109623731916357)
            ·
              refine ⟨7177084385270554449734317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38277783388109623731916357 7177084385270554449734317)
              ·
                refine ⟨2691406644476457918650369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7177084385270554449734317 2691406644476457918650369)
                ·
                  refine ⟨2018554983357343438987777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2691406644476457918650369 2018554983357343438987777)
                  ·
                    refine ⟨1513916237518007579240833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2018554983357343438987777 1513916237518007579240833)
                    ·
                      refine ⟨1135437178138505684430625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1513916237518007579240833 1135437178138505684430625)
                      ·
                        rfl

theorem cell23_2211256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 3, 2, 2, 2].length) (baseStart_2211256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2211256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2211256 prefixEnd_2211256 := by exact prefixLift 2211256
  have htrace : WordTrace (prefixWord ++ tailWord_2211256) baseStart_2211256 baseEnd_2211256 := by
    simpa [prefixWord, tailWord_2211256, baseEnd_2211256] using wordTrace_append hprefix tailTrace_2211256
  have hstable : (prefixWord ++ tailWord_2211256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211256).length < 2 ^ (prefixWord ++ tailWord_2211256).sum := by decide
  have hdescent : baseEnd_2211256 < baseStart_2211256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211272 : List Nat := [2, 1, 3, 1, 3, 1, 1, 2, 1, 5, 3]
def baseStart_2211272 : Nat := 118140960795 + 2211272 * 2 ^ 59
def prefixEnd_2211272 : Nat := 4983230072969 + 3 ^ 40 * 2211272 * 2
def baseEnd_2211272 : Nat := 1135445393828977621830551

theorem tailTrace_2211272 : CollatzResearch.WordTrace tailWord_2211272 prefixEnd_2211272 1135445393828977621830551 := by
  unfold tailWord_2211272
  simp only [CollatzResearch.WordTrace]
  refine ⟨40325857822473337018022035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53767810429964449357362713 40325857822473337018022035)
  ·
    refine ⟨60488786733710005527033053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40325857822473337018022035 60488786733710005527033053)
    ·
      refine ⟨22683295025141252072637395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60488786733710005527033053 22683295025141252072637395)
      ·
        refine ⟨34024942537711878108956093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22683295025141252072637395 34024942537711878108956093)
        ·
          refine ⟨12759353451641954290858535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34024942537711878108956093 12759353451641954290858535)
          ·
            refine ⟨19139030177462931436287803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12759353451641954290858535 19139030177462931436287803)
            ·
              refine ⟨28708545266194397154431705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19139030177462931436287803 28708545266194397154431705)
              ·
                refine ⟨21531408949645797865823779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28708545266194397154431705 21531408949645797865823779)
                ·
                  refine ⟨32297113424468696798735669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21531408949645797865823779 32297113424468696798735669)
                  ·
                    refine ⟨3027854383543940324881469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32297113424468696798735669 3027854383543940324881469)
                    ·
                      refine ⟨1135445393828977621830551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3027854383543940324881469 1135445393828977621830551)
                      ·
                        rfl

theorem cell23_2211272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 1, 5, 3].length) (baseStart_2211272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2211272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2211272 prefixEnd_2211272 := by exact prefixLift 2211272
  have htrace : WordTrace (prefixWord ++ tailWord_2211272) baseStart_2211272 baseEnd_2211272 := by
    simpa [prefixWord, tailWord_2211272, baseEnd_2211272] using wordTrace_append hprefix tailTrace_2211272
  have hstable : (prefixWord ++ tailWord_2211272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211272).length < 2 ^ (prefixWord ++ tailWord_2211272).sum := by decide
  have hdescent : baseEnd_2211272 < baseStart_2211272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211312 : List Nat := [2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 4]
def baseStart_2211312 : Nat := 118140960795 + 2211312 * 2 ^ 59
def prefixEnd_2211312 : Nat := 4983230072969 + 3 ^ 40 * 2211312 * 2
def baseEnd_2211312 : Nat := 1135465933055157465330367

theorem tailTrace_2211312 : CollatzResearch.WordTrace tailWord_2211312 prefixEnd_2211312 1135465933055157465330367 := by
  unfold tailWord_2211312
  simp only [CollatzResearch.WordTrace]
  refine ⟨40326587282400880433750095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53768783043201173911666793 40326587282400880433750095)
  ·
    refine ⟨60489880923601320650625143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40326587282400880433750095 60489880923601320650625143)
    ·
      refine ⟨90734821385401980975937715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60489880923601320650625143 90734821385401980975937715)
      ·
        refine ⟨136102232078102971463906573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90734821385401980975937715 136102232078102971463906573)
        ·
          refine ⟨51038337029288614298964965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136102232078102971463906573 51038337029288614298964965)
          ·
            refine ⟨9569688192991615181055931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51038337029288614298964965 9569688192991615181055931)
            ·
              refine ⟨14354532289487422771583897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9569688192991615181055931 14354532289487422771583897)
              ·
                refine ⟨10765899217115567078687923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14354532289487422771583897 10765899217115567078687923)
                ·
                  refine ⟨16148848825673350618031885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10765899217115567078687923 16148848825673350618031885)
                  ·
                    refine ⟨6055818309627506481761957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16148848825673350618031885 6055818309627506481761957)
                    ·
                      refine ⟨1135465933055157465330367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6055818309627506481761957 1135465933055157465330367)
                      ·
                        rfl

theorem cell23_2211312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 4].length) (baseStart_2211312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2211312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2211312 prefixEnd_2211312 := by exact prefixLift 2211312
  have htrace : WordTrace (prefixWord ++ tailWord_2211312) baseStart_2211312 baseEnd_2211312 := by
    simpa [prefixWord, tailWord_2211312, baseEnd_2211312] using wordTrace_append hprefix tailTrace_2211312
  have hstable : (prefixWord ++ tailWord_2211312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211312).length < 2 ^ (prefixWord ++ tailWord_2211312).sum := by decide
  have hdescent : baseEnd_2211312 < baseStart_2211312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211349 : List Nat := [1, 3, 2, 1, 3, 2, 1, 1, 4, 2, 3]
def baseStart_2211349 : Nat := 118140960795 + 2211349 * 2 ^ 59
def prefixEnd_2211349 : Nat := 4983230072969 + 3 ^ 40 * 2211349 * 2
def baseEnd_2211349 : Nat := 1135484931839373820567697

theorem tailTrace_2211349 : CollatzResearch.WordTrace tailWord_2211349 prefixEnd_2211349 1135484931839373820567697 := by
  unfold tailWord_2211349
  simp only [CollatzResearch.WordTrace]
  refine ⟨80654524065667716186597101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53769682710445144124398067 80654524065667716186597101)
  ·
    refine ⟨30245446524625393569973913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80654524065667716186597101 30245446524625393569973913)
    ·
      refine ⟨22684084893469045177480435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30245446524625393569973913 22684084893469045177480435)
      ·
        refine ⟨34026127340203567766220653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22684084893469045177480435 34026127340203567766220653)
        ·
          refine ⟨12759797752576337912332745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34026127340203567766220653 12759797752576337912332745)
          ·
            refine ⟨9569848314432253434249559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12759797752576337912332745 9569848314432253434249559)
            ·
              refine ⟨14354772471648380151374339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9569848314432253434249559 14354772471648380151374339)
              ·
                refine ⟨21532158707472570227061509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14354772471648380151374339 21532158707472570227061509)
                ·
                  refine ⟨4037279757651106917574033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21532158707472570227061509 4037279757651106917574033)
                  ·
                    refine ⟨3027959818238330188180525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4037279757651106917574033 3027959818238330188180525)
                    ·
                      refine ⟨1135484931839373820567697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3027959818238330188180525 1135484931839373820567697)
                      ·
                        rfl

theorem cell23_2211349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 4, 2, 3].length) (baseStart_2211349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2211349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2211349 prefixEnd_2211349 := by exact prefixLift 2211349
  have htrace : WordTrace (prefixWord ++ tailWord_2211349) baseStart_2211349 baseEnd_2211349 := by
    simpa [prefixWord, tailWord_2211349, baseEnd_2211349] using wordTrace_append hprefix tailTrace_2211349
  have hstable : (prefixWord ++ tailWord_2211349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211349).length < 2 ^ (prefixWord ++ tailWord_2211349).sum := by decide
  have hdescent : baseEnd_2211349 < baseStart_2211349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211358 : List Nat := [4, 3, 3, 1, 2, 1, 2, 1, 2, 2, 2]
def baseStart_2211358 : Nat := 118140960795 + 2211358 * 2 ^ 59
def prefixEnd_2211358 : Nat := 4983230072969 + 3 ^ 40 * 2211358 * 2
def baseEnd_2211358 : Nat := 1135489553165264285355157

theorem tailTrace_2211358 : CollatzResearch.WordTrace tailWord_2211358 prefixEnd_2211358 1135489553165264285355157 := by
  unfold tailWord_2211358
  simp only [CollatzResearch.WordTrace]
  refine ⟨10081856540329388840459341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53769901548423407149116485 10081856540329388840459341)
  ·
    refine ⟨3780696202623520815172253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10081856540329388840459341 3780696202623520815172253)
    ·
      refine ⟨1417761075983820305689595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3780696202623520815172253 1417761075983820305689595)
      ·
        refine ⟨2126641613975730458534393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1417761075983820305689595 2126641613975730458534393)
        ·
          refine ⟨1594981210481797843900795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2126641613975730458534393 1594981210481797843900795)
          ·
            refine ⟨2392471815722696765851193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1594981210481797843900795 2392471815722696765851193)
            ·
              refine ⟨1794353861792022574388395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2392471815722696765851193 1794353861792022574388395)
              ·
                refine ⟨2691530792688033861582593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1794353861792022574388395 2691530792688033861582593)
                ·
                  refine ⟨2018648094516025396186945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2691530792688033861582593 2018648094516025396186945)
                  ·
                    refine ⟨1513986070887019047140209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2018648094516025396186945 1513986070887019047140209)
                    ·
                      refine ⟨1135489553165264285355157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1513986070887019047140209 1135489553165264285355157)
                      ·
                        rfl

theorem cell23_2211358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_2211358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2211358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2211358 prefixEnd_2211358 := by exact prefixLift 2211358
  have htrace : WordTrace (prefixWord ++ tailWord_2211358) baseStart_2211358 baseEnd_2211358 := by
    simpa [prefixWord, tailWord_2211358, baseEnd_2211358] using wordTrace_append hprefix tailTrace_2211358
  have hstable : (prefixWord ++ tailWord_2211358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211358).length < 2 ^ (prefixWord ++ tailWord_2211358).sum := by decide
  have hdescent : baseEnd_2211358 < baseStart_2211358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211429 : List Nat := [1, 3, 1, 3, 3, 1, 1, 3, 1, 6]
def baseStart_2211429 : Nat := 118140960795 + 2211429 * 2 ^ 59
def prefixEnd_2211429 : Nat := 4983230072969 + 3 ^ 40 * 2211429 * 2
def baseEnd_2211429 : Nat := 378508670097244502522443

theorem tailTrace_2211429 : CollatzResearch.WordTrace tailWord_2211429 prefixEnd_2211429 378508670097244502522443 := by
  unfold tailWord_2211429
  simp only [CollatzResearch.WordTrace]
  refine ⟨80657441905377889849509341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53771627936918593233006227 80657441905377889849509341)
  ·
    refine ⟨30246540714516708693566003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80657441905377889849509341 30246540714516708693566003)
    ·
      refine ⟨45369811071775063040349005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30246540714516708693566003 45369811071775063040349005)
      ·
        refine ⟨17013679151915648640130877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45369811071775063040349005 17013679151915648640130877)
        ·
          refine ⟨6380129681968368240049079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17013679151915648640130877 6380129681968368240049079)
          ·
            refine ⟨9570194522952552360073619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6380129681968368240049079 9570194522952552360073619)
            ·
              refine ⟨14355291784428828540110429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9570194522952552360073619 14355291784428828540110429)
              ·
                refine ⟨5383234419160810702541411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14355291784428828540110429 5383234419160810702541411)
                ·
                  refine ⟨8074851628741216053812117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5383234419160810702541411 8074851628741216053812117)
                  ·
                    refine ⟨378508670097244502522443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8074851628741216053812117 378508670097244502522443)
                    ·
                      rfl

theorem cell23_2211429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 6].length) (baseStart_2211429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2211429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2211429 prefixEnd_2211429 := by exact prefixLift 2211429
  have htrace : WordTrace (prefixWord ++ tailWord_2211429) baseStart_2211429 baseEnd_2211429 := by
    simpa [prefixWord, tailWord_2211429, baseEnd_2211429] using wordTrace_append hprefix tailTrace_2211429
  have hstable : (prefixWord ++ tailWord_2211429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211429).length < 2 ^ (prefixWord ++ tailWord_2211429).sum := by decide
  have hdescent : baseEnd_2211429 < baseStart_2211429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211446 : List Nat := [5, 1, 1, 2, 2, 1, 2, 2, 1, 6]
def baseStart_2211446 : Nat := 118140960795 + 2211446 * 2 ^ 59
def prefixEnd_2211446 : Nat := 4983230072969 + 3 ^ 40 * 2211446 * 2
def baseEnd_2211446 : Nat := 378511579820953313684917

theorem tailTrace_2211446 : CollatzResearch.WordTrace tailWord_2211446 prefixEnd_2211446 378511579820953313684917 := by
  unfold tailWord_2211446
  simp only [CollatzResearch.WordTrace]
  refine ⟨5041128871644768859554887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53772041297544201168585461 5041128871644768859554887)
  ·
    refine ⟨7561693307467153289332331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5041128871644768859554887 7561693307467153289332331)
    ·
      refine ⟨11342539961200729933998497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7561693307467153289332331 11342539961200729933998497)
      ·
        refine ⟨8506904970900547450498873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11342539961200729933998497 8506904970900547450498873)
        ·
          refine ⟨6380178728175410587874155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8506904970900547450498873 6380178728175410587874155)
          ·
            refine ⟨9570268092263115881811233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6380178728175410587874155 9570268092263115881811233)
            ·
              refine ⟨7177701069197336911358425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9570268092263115881811233 7177701069197336911358425)
              ·
                refine ⟨5383275801898002683518819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7177701069197336911358425 5383275801898002683518819)
                ·
                  refine ⟨8074913702847004025278229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5383275801898002683518819 8074913702847004025278229)
                  ·
                    refine ⟨378511579820953313684917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8074913702847004025278229 378511579820953313684917)
                    ·
                      rfl

theorem cell23_2211446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_2211446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2211446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2211446 prefixEnd_2211446 := by exact prefixLift 2211446
  have htrace : WordTrace (prefixWord ++ tailWord_2211446) baseStart_2211446 baseEnd_2211446 := by
    simpa [prefixWord, tailWord_2211446, baseEnd_2211446] using wordTrace_append hprefix tailTrace_2211446
  have hstable : (prefixWord ++ tailWord_2211446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211446).length < 2 ^ (prefixWord ++ tailWord_2211446).sum := by decide
  have hdescent : baseEnd_2211446 < baseStart_2211446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211449 : List Nat := [1, 2, 1, 3, 3, 1, 1, 4, 1, 2, 4]
def baseStart_2211449 : Nat := 118140960795 + 2211449 * 2 ^ 59
def prefixEnd_2211449 : Nat := 4983230072969 + 3 ^ 40 * 2211449 * 2
def baseEnd_2211449 : Nat := 1135536279904823429317237

theorem tailTrace_2211449 : CollatzResearch.WordTrace tailWord_2211449 prefixEnd_2211449 1135536279904823429317237 := by
  unfold tailWord_2211449
  simp only [CollatzResearch.WordTrace]
  refine ⟨80658171365305433265237401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53772114243536955510158267 80658171365305433265237401)
  ·
    refine ⟨60493628523979074948928051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80658171365305433265237401 60493628523979074948928051)
    ·
      refine ⟨90740442785968612423392077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60493628523979074948928051 90740442785968612423392077)
      ·
        refine ⟨34027666044738229658772029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90740442785968612423392077 34027666044738229658772029)
        ·
          refine ⟨12760374766776836122039511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34027666044738229658772029 12760374766776836122039511)
          ·
            refine ⟨19140562150165254183059267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12760374766776836122039511 19140562150165254183059267)
            ·
              refine ⟨28710843225247881274588901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19140562150165254183059267 28710843225247881274588901)
              ·
                refine ⟨5383283104733977738985419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28710843225247881274588901 5383283104733977738985419)
                ·
                  refine ⟨8074924657100966608478129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5383283104733977738985419 8074924657100966608478129)
                  ·
                    refine ⟨6056193492825724956358597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8074924657100966608478129 6056193492825724956358597)
                    ·
                      refine ⟨1135536279904823429317237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6056193492825724956358597 1135536279904823429317237)
                      ·
                        rfl

theorem cell23_2211449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_2211449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2211449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2211449 prefixEnd_2211449 := by exact prefixLift 2211449
  have htrace : WordTrace (prefixWord ++ tailWord_2211449) baseStart_2211449 baseEnd_2211449 := by
    simpa [prefixWord, tailWord_2211449, baseEnd_2211449] using wordTrace_append hprefix tailTrace_2211449
  have hstable : (prefixWord ++ tailWord_2211449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211449).length < 2 ^ (prefixWord ++ tailWord_2211449).sum := by decide
  have hdescent : baseEnd_2211449 < baseStart_2211449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211453 : List Nat := [1, 4, 1, 1, 4, 1, 4, 1, 1, 1, 4]
def baseStart_2211453 : Nat := 118140960795 + 2211453 * 2 ^ 59
def prefixEnd_2211453 : Nat := 4983230072969 + 3 ^ 40 * 2211453 * 2
def baseEnd_2211453 : Nat := 1135538333827441413667219

theorem tailTrace_2211453 : CollatzResearch.WordTrace tailWord_2211453 prefixEnd_2211453 1135538333827441413667219 := by
  unfold tailWord_2211453
  simp only [CollatzResearch.WordTrace]
  refine ⟨80658317257290941948383013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53772211504860627965588675 80658317257290941948383013)
  ·
    refine ⟨15123434485742051615321815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80658317257290941948383013 15123434485742051615321815)
    ·
      refine ⟨22685151728613077422982723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15123434485742051615321815 22685151728613077422982723)
      ·
        refine ⟨34027727592919616134474085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22685151728613077422982723 34027727592919616134474085)
        ·
          refine ⟨6380198923672428025213891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34027727592919616134474085 6380198923672428025213891)
          ·
            refine ⟨9570298385508642037820837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6380198923672428025213891 9570298385508642037820837)
            ·
              refine ⟨1794430947282870382091407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9570298385508642037820837 1794430947282870382091407)
              ·
                refine ⟨2691646420924305573137111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1794430947282870382091407 2691646420924305573137111)
                ·
                  refine ⟨4037469631386458359705667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2691646420924305573137111 4037469631386458359705667)
                  ·
                    refine ⟨6056204447079687539558501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4037469631386458359705667 6056204447079687539558501)
                    ·
                      refine ⟨1135538333827441413667219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6056204447079687539558501 1135538333827441413667219)
                      ·
                        rfl

theorem cell23_2211453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 1, 1, 1, 4].length) (baseStart_2211453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2211453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2211453 prefixEnd_2211453 := by exact prefixLift 2211453
  have htrace : WordTrace (prefixWord ++ tailWord_2211453) baseStart_2211453 baseEnd_2211453 := by
    simpa [prefixWord, tailWord_2211453, baseEnd_2211453] using wordTrace_append hprefix tailTrace_2211453
  have hstable : (prefixWord ++ tailWord_2211453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211453).length < 2 ^ (prefixWord ++ tailWord_2211453).sum := by decide
  have hdescent : baseEnd_2211453 < baseStart_2211453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211456 : List Nat := [2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 3]
def baseStart_2211456 : Nat := 118140960795 + 2211456 * 2 ^ 59
def prefixEnd_2211456 : Nat := 4983230072969 + 3 ^ 40 * 2211456 * 2
def baseEnd_2211456 : Nat := 1135539874269404901929705

theorem tailTrace_2211456 : CollatzResearch.WordTrace tailWord_2211456 prefixEnd_2211456 1135539874269404901929705 := by
  unfold tailWord_2211456
  simp only [CollatzResearch.WordTrace]
  refine ⟨40329213338140036730371111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53772284450853382307161481 40329213338140036730371111)
  ·
    refine ⟨60493820007210055095556667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40329213338140036730371111 60493820007210055095556667)
    ·
      refine ⟨90740730010815082643335001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60493820007210055095556667 90740730010815082643335001)
      ·
        refine ⟨68055547508111311982501251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90740730010815082643335001 68055547508111311982501251)
        ·
          refine ⟨102083321262166967973751877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68055547508111311982501251 102083321262166967973751877)
          ·
            refine ⟨19140622736656306495078477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102083321262166967973751877 19140622736656306495078477)
            ·
              refine ⟨7177733526246114935654429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19140622736656306495078477 7177733526246114935654429)
              ·
                refine ⟨2691650072342293100870411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7177733526246114935654429 2691650072342293100870411)
                ·
                  refine ⟨4037475108513439651305617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2691650072342293100870411 4037475108513439651305617)
                  ·
                    refine ⟨3028106331385079738479213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4037475108513439651305617 3028106331385079738479213)
                    ·
                      refine ⟨1135539874269404901929705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3028106331385079738479213 1135539874269404901929705)
                      ·
                        rfl

theorem cell23_2211456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 3].length) (baseStart_2211456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2211456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2211456 prefixEnd_2211456 := by exact prefixLift 2211456
  have htrace : WordTrace (prefixWord ++ tailWord_2211456) baseStart_2211456 baseEnd_2211456 := by
    simpa [prefixWord, tailWord_2211456, baseEnd_2211456] using wordTrace_append hprefix tailTrace_2211456
  have hstable : (prefixWord ++ tailWord_2211456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211456).length < 2 ^ (prefixWord ++ tailWord_2211456).sum := by decide
  have hdescent : baseEnd_2211456 < baseStart_2211456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211463 : List Nat := [1, 1, 4, 2, 1, 5, 1, 2, 2, 4]
def baseStart_2211463 : Nat := 118140960795 + 2211463 * 2 ^ 59
def prefixEnd_2211463 : Nat := 4983230072969 + 3 ^ 40 * 2211463 * 2
def baseEnd_2211463 : Nat := 378514489544662124847391

theorem tailTrace_2211463 : CollatzResearch.WordTrace tailWord_2211463 prefixEnd_2211463 378514489544662124847391 := by
  unfold tailWord_2211463
  simp only [CollatzResearch.WordTrace]
  refine ⟨80658681987254713656247043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53772454658169809104164695 80658681987254713656247043)
  ·
    refine ⟨120988022980882070484370565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80658681987254713656247043 120988022980882070484370565)
    ·
      refine ⟨22685254308915388215819481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120988022980882070484370565 22685254308915388215819481)
      ·
        refine ⟨17013940731686541161864611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22685254308915388215819481 17013940731686541161864611)
        ·
          refine ⟨25520911097529811742796917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17013940731686541161864611 25520911097529811742796917)
          ·
            refine ⟨2392585415393419850887211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25520911097529811742796917 2392585415393419850887211)
            ·
              refine ⟨3588878123090129776330817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2392585415393419850887211 3588878123090129776330817)
              ·
                refine ⟨2691658592317597332248113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3588878123090129776330817 2691658592317597332248113)
                ·
                  refine ⟨2018743944238197999186085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2691658592317597332248113 2018743944238197999186085)
                  ·
                    refine ⟨378514489544662124847391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2018743944238197999186085 378514489544662124847391)
                    ·
                      rfl

theorem cell23_2211463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 2, 2, 4].length) (baseStart_2211463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2211463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2211463 prefixEnd_2211463 := by exact prefixLift 2211463
  have htrace : WordTrace (prefixWord ++ tailWord_2211463) baseStart_2211463 baseEnd_2211463 := by
    simpa [prefixWord, tailWord_2211463, baseEnd_2211463] using wordTrace_append hprefix tailTrace_2211463
  have hstable : (prefixWord ++ tailWord_2211463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211463).length < 2 ^ (prefixWord ++ tailWord_2211463).sum := by decide
  have hdescent : baseEnd_2211463 < baseStart_2211463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211470 : List Nat := [4, 1, 1, 3, 1, 3, 2, 1, 3, 2, 2]
def baseStart_2211470 : Nat := 118140960795 + 2211470 * 2 ^ 59
def prefixEnd_2211470 : Nat := 4983230072969 + 3 ^ 40 * 2211470 * 2
def baseEnd_2211470 : Nat := 1135547062998567847154641

theorem tailTrace_2211470 : CollatzResearch.WordTrace tailWord_2211470 prefixEnd_2211470 1135547062998567847154641 := by
  unfold tailWord_2211470
  simp only [CollatzResearch.WordTrace]
  refine ⟨10082367162278669231468983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53772624865486235901167909 10082367162278669231468983)
  ·
    refine ⟨15123550743418003847203475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10082367162278669231468983 15123550743418003847203475)
    ·
      refine ⟨22685326115127005770805213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15123550743418003847203475 22685326115127005770805213)
      ·
        refine ⟨8506997293172627164051955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22685326115127005770805213 8506997293172627164051955)
        ·
          refine ⟨12760495939758940746077933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8506997293172627164051955 12760495939758940746077933)
          ·
            refine ⟨4785185977409602779779225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12760495939758940746077933 4785185977409602779779225)
            ·
              refine ⟨3588889483057202084834419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4785185977409602779779225 3588889483057202084834419)
              ·
                refine ⟨5383334224585803127251629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3588889483057202084834419 5383334224585803127251629)
                ·
                  refine ⟨2018750334219676172719361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5383334224585803127251629 2018750334219676172719361)
                  ·
                    refine ⟨1514062750664757129539521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2018750334219676172719361 1514062750664757129539521)
                    ·
                      refine ⟨1135547062998567847154641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1514062750664757129539521 1135547062998567847154641)
                      ·
                        rfl

theorem cell23_2211470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_2211470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2211470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2211470 prefixEnd_2211470 := by exact prefixLift 2211470
  have htrace : WordTrace (prefixWord ++ tailWord_2211470) baseStart_2211470 baseEnd_2211470 := by
    simpa [prefixWord, tailWord_2211470, baseEnd_2211470] using wordTrace_append hprefix tailTrace_2211470
  have hstable : (prefixWord ++ tailWord_2211470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211470).length < 2 ^ (prefixWord ++ tailWord_2211470).sum := by decide
  have hdescent : baseEnd_2211470 < baseStart_2211470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211472 : List Nat := [2, 1, 1, 1, 1, 1, 3, 3, 1, 9]
def baseStart_2211472 : Nat := 118140960795 + 2211472 * 2 ^ 59
def prefixEnd_2211472 : Nat := 4983230072969 + 3 ^ 40 * 2211472 * 2
def baseEnd_2211472 : Nat := 378516029986625613109877

theorem tailTrace_2211472 : CollatzResearch.WordTrace tailWord_2211472 prefixEnd_2211472 378516029986625613109877 := by
  unfold tailWord_2211472
  simp only [CollatzResearch.WordTrace]
  refine ⟨40329505122111054096662335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53772673496148072128883113 40329505122111054096662335)
  ·
    refine ⟨60494257683166581144993503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40329505122111054096662335 60494257683166581144993503)
    ·
      refine ⟨90741386524749871717490255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60494257683166581144993503 90741386524749871717490255)
      ·
        refine ⟨136112079787124807576235383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90741386524749871717490255 136112079787124807576235383)
        ·
          refine ⟨204168119680687211364353075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136112079787124807576235383 204168119680687211364353075)
          ·
            refine ⟨306252179521030817046529613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204168119680687211364353075 306252179521030817046529613)
            ·
              refine ⟨114844567320386556392448605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 306252179521030817046529613 114844567320386556392448605)
              ·
                refine ⟨43066712745144958647168227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114844567320386556392448605 43066712745144958647168227)
                ·
                  refine ⟨64600069117717437970752341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43066712745144958647168227 64600069117717437970752341)
                  ·
                    refine ⟨378516029986625613109877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 64600069117717437970752341 378516029986625613109877)
                    ·
                      rfl

theorem cell23_2211472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 1, 9].length) (baseStart_2211472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2211472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2211472 prefixEnd_2211472 := by exact prefixLift 2211472
  have htrace : WordTrace (prefixWord ++ tailWord_2211472) baseStart_2211472 baseEnd_2211472 := by
    simpa [prefixWord, tailWord_2211472, baseEnd_2211472] using wordTrace_append hprefix tailTrace_2211472
  have hstable : (prefixWord ++ tailWord_2211472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211472).length < 2 ^ (prefixWord ++ tailWord_2211472).sum := by decide
  have hdescent : baseEnd_2211472 < baseStart_2211472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211513 : List Nat := [1, 2, 1, 4, 1, 1, 4, 3, 1, 3, 2]
def baseStart_2211513 : Nat := 118140960795 + 2211513 * 2 ^ 59
def prefixEnd_2211513 : Nat := 4983230072969 + 3 ^ 40 * 2211513 * 2
def baseEnd_2211513 : Nat := 1135569142666711178916943

theorem tailTrace_2211513 : CollatzResearch.WordTrace tailWord_2211513 prefixEnd_2211513 1135569142666711178916943 := by
  unfold tailWord_2211513
  simp only [CollatzResearch.WordTrace]
  refine ⟨80660505637073572195567193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53773670424715714797044795 80660505637073572195567193)
  ·
    refine ⟨60495379227805179146675395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80660505637073572195567193 60495379227805179146675395)
    ·
      refine ⟨90743068841707768720013093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60495379227805179146675395 90743068841707768720013093)
      ·
        refine ⟨17014325407820206635002455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90743068841707768720013093 17014325407820206635002455)
        ·
          refine ⟨25521488111730309952503683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17014325407820206635002455 25521488111730309952503683)
          ·
            refine ⟨38282232167595464928755525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25521488111730309952503683 38282232167595464928755525)
            ·
              refine ⟨7177918531424149674141661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38282232167595464928755525 7177918531424149674141661)
              ·
                refine ⟨2691719449284056127803123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7177918531424149674141661 2691719449284056127803123)
                ·
                  refine ⟨4037579173926084191704685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2691719449284056127803123 4037579173926084191704685)
                  ·
                    refine ⟨1514092190222281571889257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4037579173926084191704685 1514092190222281571889257)
                    ·
                      refine ⟨1135569142666711178916943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1514092190222281571889257 1135569142666711178916943)
                      ·
                        rfl

theorem cell23_2211513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 3, 1, 3, 2].length) (baseStart_2211513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2211513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2211513 prefixEnd_2211513 := by exact prefixLift 2211513
  have htrace : WordTrace (prefixWord ++ tailWord_2211513) baseStart_2211513 baseEnd_2211513 := by
    simpa [prefixWord, tailWord_2211513, baseEnd_2211513] using wordTrace_append hprefix tailTrace_2211513
  have hstable : (prefixWord ++ tailWord_2211513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211513).length < 2 ^ (prefixWord ++ tailWord_2211513).sum := by decide
  have hdescent : baseEnd_2211513 < baseStart_2211513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211579 : List Nat := [1, 1, 1, 1, 1, 3, 1, 5, 4, 5]
def baseStart_2211579 : Nat := 118140960795 + 2211579 * 2 ^ 59
def prefixEnd_2211579 : Nat := 4983230072969 + 3 ^ 40 * 2211579 * 2
def baseEnd_2211579 : Nat := 378534344129969306897213

theorem tailTrace_2211579 : CollatzResearch.WordTrace tailWord_2211579 prefixEnd_2211579 378534344129969306897213 := by
  unfold tailWord_2211579
  simp only [CollatzResearch.WordTrace]
  refine ⟨80662912854834465467469791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53775275236556310311646527 80662912854834465467469791)
  ·
    refine ⟨120994369282251698201204687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80662912854834465467469791 120994369282251698201204687)
    ·
      refine ⟨181491553923377547301807031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120994369282251698201204687 181491553923377547301807031)
      ·
        refine ⟨272237330885066320952710547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181491553923377547301807031 272237330885066320952710547)
        ·
          refine ⟨408355996327599481429065821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272237330885066320952710547 408355996327599481429065821)
          ·
            refine ⟨153133498622849805535899683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 408355996327599481429065821 153133498622849805535899683)
            ·
              refine ⟨229700247934274708303849525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153133498622849805535899683 229700247934274708303849525)
              ·
                refine ⟨21534398243838253903485893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 229700247934274708303849525 21534398243838253903485893)
                ·
                  refine ⟨4037699670719672606903605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21534398243838253903485893 4037699670719672606903605)
                  ·
                    refine ⟨378534344129969306897213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4037699670719672606903605 378534344129969306897213)
                    ·
                      rfl

theorem cell23_2211579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4, 5].length) (baseStart_2211579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2211579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2211579 prefixEnd_2211579 := by exact prefixLift 2211579
  have htrace : WordTrace (prefixWord ++ tailWord_2211579) baseStart_2211579 baseEnd_2211579 := by
    simpa [prefixWord, tailWord_2211579, baseEnd_2211579] using wordTrace_append hprefix tailTrace_2211579
  have hstable : (prefixWord ++ tailWord_2211579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211579).length < 2 ^ (prefixWord ++ tailWord_2211579).sum := by decide
  have hdescent : baseEnd_2211579 < baseStart_2211579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211583 : List Nat := [1, 1, 2, 2, 1, 3, 6, 2, 5]
def baseStart_2211583 : Nat := 118140960795 + 2211583 * 2 ^ 59
def prefixEnd_2211583 : Nat := 4983230072969 + 3 ^ 40 * 2211583 * 2
def baseEnd_2211583 : Nat := 126178342923613989449069

theorem tailTrace_2211583 : CollatzResearch.WordTrace tailWord_2211583 prefixEnd_2211583 126178342923613989449069 := by
  unfold tailWord_2211583
  simp only [CollatzResearch.WordTrace]
  refine ⟨80663058746819974150615403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53775372497879982767076935 80663058746819974150615403)
  ·
    refine ⟨120994588120229961225923105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80663058746819974150615403 120994588120229961225923105)
    ·
      refine ⟨90745941090172470919442329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120994588120229961225923105 90745941090172470919442329)
      ·
        refine ⟨68059455817629353189581747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90745941090172470919442329 68059455817629353189581747)
        ·
          refine ⟨102089183726444029784372621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68059455817629353189581747 102089183726444029784372621)
          ·
            refine ⟨38283443897416511169139733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102089183726444029784372621 38283443897416511169139733)
            ·
              refine ⟨1794536432691398961053425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38283443897416511169139733 1794536432691398961053425)
              ·
                refine ⟨1345902324518549220790069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1794536432691398961053425 1345902324518549220790069)
                ·
                  refine ⟨126178342923613989449069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1345902324518549220790069 126178342923613989449069)
                  ·
                    rfl

theorem cell23_2211583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 2, 5].length) (baseStart_2211583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2211583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2211583 prefixEnd_2211583 := by exact prefixLift 2211583
  have htrace : WordTrace (prefixWord ++ tailWord_2211583) baseStart_2211583 baseEnd_2211583 := by
    simpa [prefixWord, tailWord_2211583, baseEnd_2211583] using wordTrace_append hprefix tailTrace_2211583
  have hstable : (prefixWord ++ tailWord_2211583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211583).length < 2 ^ (prefixWord ++ tailWord_2211583).sum := by decide
  have hdescent : baseEnd_2211583 < baseStart_2211583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211616 : List Nat := [2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 4]
def baseStart_2211616 : Nat := 118140960795 + 2211616 * 2 ^ 59
def prefixEnd_2211616 : Nat := 4983230072969 + 3 ^ 40 * 2211616 * 2
def baseEnd_2211616 : Nat := 1135622031174124275928969

theorem tailTrace_2211616 : CollatzResearch.WordTrace tailWord_2211616 prefixEnd_2211616 1135622031174124275928969 := by
  unfold tailWord_2211616
  simp only [CollatzResearch.WordTrace]
  refine ⟨40332131177850210393283351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53776174903800280524377801 40332131177850210393283351)
  ·
    refine ⟨60498196766775315589925027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40332131177850210393283351 60498196766775315589925027)
    ·
      refine ⟨90747295150162973384887541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60498196766775315589925027 90747295150162973384887541)
      ·
        refine ⟨8507558920327778754833207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 90747295150162973384887541 8507558920327778754833207)
        ·
          refine ⟨12761338380491668132249811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8507558920327778754833207 12761338380491668132249811)
          ·
            refine ⟨19142007570737502198374717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12761338380491668132249811 19142007570737502198374717)
            ·
              refine ⟨7178252839026563324390519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19142007570737502198374717 7178252839026563324390519)
              ·
                refine ⟨10767379258539844986585779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7178252839026563324390519 10767379258539844986585779)
                ·
                  refine ⟨16151068887809767479878669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10767379258539844986585779 16151068887809767479878669)
                  ·
                    refine ⟨6056650832928662804954501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16151068887809767479878669 6056650832928662804954501)
                    ·
                      refine ⟨1135622031174124275928969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6056650832928662804954501 1135622031174124275928969)
                      ·
                        rfl

theorem cell23_2211616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_2211616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2211616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2211616 prefixEnd_2211616 := by exact prefixLift 2211616
  have htrace : WordTrace (prefixWord ++ tailWord_2211616) baseStart_2211616 baseEnd_2211616 := by
    simpa [prefixWord, tailWord_2211616, baseEnd_2211616] using wordTrace_append hprefix tailTrace_2211616
  have hstable : (prefixWord ++ tailWord_2211616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211616).length < 2 ^ (prefixWord ++ tailWord_2211616).sum := by decide
  have hdescent : baseEnd_2211616 < baseStart_2211616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211633 : List Nat := [1, 2, 2, 3, 2, 2, 1, 2, 2, 4, 2]
def baseStart_2211633 : Nat := 118140960795 + 2211633 * 2 ^ 59
def prefixEnd_2211633 : Nat := 4983230072969 + 3 ^ 40 * 2211633 * 2
def baseEnd_2211633 : Nat := 1135630760345250709416391

theorem tailTrace_2211633 : CollatzResearch.WordTrace tailWord_2211633 prefixEnd_2211633 1135630760345250709416391 := by
  unfold tailWord_2211633
  simp only [CollatzResearch.WordTrace]
  refine ⟨80664882396638832689935553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53776588264425888459957035 80664882396638832689935553)
  ·
    refine ⟨60498661797479124517451665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80664882396638832689935553 60498661797479124517451665)
    ·
      refine ⟨45373996348109343388088749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60498661797479124517451665 45373996348109343388088749)
      ·
        refine ⟨17015248630541003770533281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45373996348109343388088749 17015248630541003770533281)
        ·
          refine ⟨12761436472905752827899961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17015248630541003770533281 12761436472905752827899961)
          ·
            refine ⟨9571077354679314620924971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12761436472905752827899961 9571077354679314620924971)
            ·
              refine ⟨14356616032018971931387457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9571077354679314620924971 14356616032018971931387457)
              ·
                refine ⟨10767462024014228948540593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14356616032018971931387457 10767462024014228948540593)
                ·
                  refine ⟨8075596518010671711405445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10767462024014228948540593 8075596518010671711405445)
                  ·
                    refine ⟨1514174347127000945888521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8075596518010671711405445 1514174347127000945888521)
                    ·
                      refine ⟨1135630760345250709416391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1514174347127000945888521 1135630760345250709416391)
                      ·
                        rfl

theorem cell23_2211633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 4, 2].length) (baseStart_2211633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2211633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2211633 prefixEnd_2211633 := by exact prefixLift 2211633
  have htrace : WordTrace (prefixWord ++ tailWord_2211633) baseStart_2211633 baseEnd_2211633 := by
    simpa [prefixWord, tailWord_2211633, baseEnd_2211633] using wordTrace_append hprefix tailTrace_2211633
  have hstable : (prefixWord ++ tailWord_2211633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211633).length < 2 ^ (prefixWord ++ tailWord_2211633).sum := by decide
  have hdescent : baseEnd_2211633 < baseStart_2211633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211694 : List Nat := [4, 1, 2, 3, 1, 2, 3, 2, 1, 4]
def baseStart_2211694 : Nat := 118140960795 + 2211694 * 2 ^ 59
def prefixEnd_2211694 : Nat := 4983230072969 + 3 ^ 40 * 2211694 * 2
def baseEnd_2211694 : Nat := 378554027555058323584537

theorem tailTrace_2211694 : CollatzResearch.WordTrace tailWord_2211694 prefixEnd_2211694 378554027555058323584537 := by
  unfold tailWord_2211694
  simp only [CollatzResearch.WordTrace]
  refine ⟨10083388406177230013488267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53778071499611893405270757 10083388406177230013488267)
  ·
    refine ⟨15125082609265845020232401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10083388406177230013488267 15125082609265845020232401)
    ·
      refine ⟨11343811956949383765174301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15125082609265845020232401 11343811956949383765174301)
      ·
        refine ⟨4253929483856018911940363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11343811956949383765174301 4253929483856018911940363)
        ·
          refine ⟨6380894225784028367910545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4253929483856018911940363 6380894225784028367910545)
          ·
            refine ⟨4785670669338021275932909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6380894225784028367910545 4785670669338021275932909)
            ·
              refine ⟨1794626501001757978474841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4785670669338021275932909 1794626501001757978474841)
              ·
                refine ⟨1345969875751318483856131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1794626501001757978474841 1345969875751318483856131)
                ·
                  refine ⟨2018954813626977725784197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1345969875751318483856131 2018954813626977725784197)
                  ·
                    refine ⟨378554027555058323584537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2018954813626977725784197 378554027555058323584537)
                    ·
                      rfl

theorem cell23_2211694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_2211694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2211694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2211694 prefixEnd_2211694 := by exact prefixLift 2211694
  have htrace : WordTrace (prefixWord ++ tailWord_2211694) baseStart_2211694 baseEnd_2211694 := by
    simpa [prefixWord, tailWord_2211694, baseEnd_2211694] using wordTrace_append hprefix tailTrace_2211694
  have hstable : (prefixWord ++ tailWord_2211694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211694).length < 2 ^ (prefixWord ++ tailWord_2211694).sum := by decide
  have hdescent : baseEnd_2211694 < baseStart_2211694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211746 : List Nat := [3, 3, 1, 2, 14]
def baseStart_2211746 : Nat := 118140960795 + 2211746 * 2 ^ 59
def prefixEnd_2211746 : Nat := 4983230072969 + 3 ^ 40 * 2211746 * 2
def baseEnd_2211746 : Nat := 1557872131219765112899

theorem tailTrace_2211746 : CollatzResearch.WordTrace tailWord_2211746 prefixEnd_2211746 1557872131219765112899 := by
  unfold tailWord_2211746
  simp only [CollatzResearch.WordTrace]
  refine ⟨20167250961307363247199773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53779335896819635325866061 20167250961307363247199773)
  ·
    refine ⟨7562719110490261217699915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20167250961307363247199773 7562719110490261217699915)
    ·
      refine ⟨11344078665735391826549873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7562719110490261217699915 11344078665735391826549873)
      ·
        refine ⟨8508058999301543869912405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11344078665735391826549873 8508058999301543869912405)
        ·
          refine ⟨1557872131219765112899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 8508058999301543869912405 1557872131219765112899)
          ·
            rfl

theorem cell23_2211746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 14].length) (baseStart_2211746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2211746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2211746 prefixEnd_2211746 := by exact prefixLift 2211746
  have htrace : WordTrace (prefixWord ++ tailWord_2211746) baseStart_2211746 baseEnd_2211746 := by
    simpa [prefixWord, tailWord_2211746, baseEnd_2211746] using wordTrace_append hprefix tailTrace_2211746
  have hstable : (prefixWord ++ tailWord_2211746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211746).length < 2 ^ (prefixWord ++ tailWord_2211746).sum := by decide
  have hdescent : baseEnd_2211746 < baseStart_2211746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211751 : List Nat := [1, 1, 6, 1, 2, 3, 2, 2, 1, 1, 3]
def baseStart_2211751 : Nat := 118140960795 + 2211751 * 2 ^ 59
def prefixEnd_2211751 : Nat := 4983230072969 + 3 ^ 40 * 2211751 * 2
def baseEnd_2211751 : Nat := 1135691351062481247740849

theorem tailTrace_2211751 : CollatzResearch.WordTrace tailWord_2211751 prefixEnd_2211751 1135691351062481247740849 := by
  unfold tailWord_2211751
  simp only [CollatzResearch.WordTrace]
  refine ⟨80669186210211338842731107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53779457473474225895154071 80669186210211338842731107)
  ·
    refine ⟨121003779315317008264096661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80669186210211338842731107 121003779315317008264096661)
    ·
      refine ⟨5672052155405484762379531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 121003779315317008264096661 5672052155405484762379531)
      ·
        refine ⟨8508078233108227143569297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5672052155405484762379531 8508078233108227143569297)
        ·
          refine ⟨6381058674831170357676973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8508078233108227143569297 6381058674831170357676973)
          ·
            refine ⟨2392897003061688884128865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6381058674831170357676973 2392897003061688884128865)
            ·
              refine ⟨1794672752296266663096649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2392897003061688884128865 1794672752296266663096649)
              ·
                refine ⟨1346004564222199997322487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1794672752296266663096649 1346004564222199997322487)
                ·
                  refine ⟨2019006846333299995983731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1346004564222199997322487 2019006846333299995983731)
                  ·
                    refine ⟨3028510269499949993975597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2019006846333299995983731 3028510269499949993975597)
                    ·
                      refine ⟨1135691351062481247740849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3028510269499949993975597 1135691351062481247740849)
                      ·
                        rfl

theorem cell23_2211751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_2211751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2211751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2211751 prefixEnd_2211751 := by exact prefixLift 2211751
  have htrace : WordTrace (prefixWord ++ tailWord_2211751) baseStart_2211751 baseEnd_2211751 := by
    simpa [prefixWord, tailWord_2211751, baseEnd_2211751] using wordTrace_append hprefix tailTrace_2211751
  have hstable : (prefixWord ++ tailWord_2211751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211751).length < 2 ^ (prefixWord ++ tailWord_2211751).sum := by decide
  have hdescent : baseEnd_2211751 < baseStart_2211751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211776 : List Nat := [2, 1, 1, 2, 3, 2, 1, 2, 2, 7]
def baseStart_2211776 : Nat := 118140960795 + 2211776 * 2 ^ 59
def prefixEnd_2211776 : Nat := 4983230072969 + 3 ^ 40 * 2211776 * 2
def baseEnd_2211776 : Nat := 378568062692947883309411

theorem tailTrace_2211776 : CollatzResearch.WordTrace tailWord_2211776 prefixEnd_2211776 378568062692947883309411 := by
  unfold tailWord_2211776
  simp only [CollatzResearch.WordTrace]
  refine ⟨40335049017560384056195591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53780065356747178741594121 40335049017560384056195591)
  ·
    refine ⟨60502573526340576084293387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40335049017560384056195591 60502573526340576084293387)
    ·
      refine ⟨90753860289510864126440081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60502573526340576084293387 90753860289510864126440081)
      ·
        refine ⟨68065395217133148094830061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90753860289510864126440081 68065395217133148094830061)
        ·
          refine ⟨25524523206424930535561273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68065395217133148094830061 25524523206424930535561273)
          ·
            refine ⟨19143392404818697901670955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25524523206424930535561273 19143392404818697901670955)
            ·
              refine ⟨28715088607228046852506433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19143392404818697901670955 28715088607228046852506433)
              ·
                refine ⟨21536316455421035139379825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28715088607228046852506433 21536316455421035139379825)
                ·
                  refine ⟨16152237341565776354534869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21536316455421035139379825 16152237341565776354534869)
                  ·
                    refine ⟨378568062692947883309411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16152237341565776354534869 378568062692947883309411)
                    ·
                      rfl

theorem cell23_2211776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 2, 7].length) (baseStart_2211776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2211776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2211776 prefixEnd_2211776 := by exact prefixLift 2211776
  have htrace : WordTrace (prefixWord ++ tailWord_2211776) baseStart_2211776 baseEnd_2211776 := by
    simpa [prefixWord, tailWord_2211776, baseEnd_2211776] using wordTrace_append hprefix tailTrace_2211776
  have hstable : (prefixWord ++ tailWord_2211776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211776).length < 2 ^ (prefixWord ++ tailWord_2211776).sum := by decide
  have hdescent : baseEnd_2211776 < baseStart_2211776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211790 : List Nat := [4, 1, 1, 1, 2, 2, 2, 2, 4, 1, 3]
def baseStart_2211790 : Nat := 118140960795 + 2211790 * 2 ^ 59
def prefixEnd_2211790 : Nat := 4983230072969 + 3 ^ 40 * 2211790 * 2
def baseEnd_2211790 : Nat := 1135711376808006595153169

theorem tailTrace_2211790 : CollatzResearch.WordTrace tailWord_2211790 prefixEnd_2211790 1135711376808006595153169 := by
  unfold tailWord_2211790
  simp only [CollatzResearch.WordTrace]
  refine ⟨10083826082133756062925103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53780405771380032335600549 10083826082133756062925103)
  ·
    refine ⟨15125739123200634094387655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10083826082133756062925103 15125739123200634094387655)
    ·
      refine ⟨22688608684800951141581483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15125739123200634094387655 22688608684800951141581483)
      ·
        refine ⟨34032913027201426712372225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22688608684800951141581483 34032913027201426712372225)
        ·
          refine ⟨25524684770401070034279169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34032913027201426712372225 25524684770401070034279169)
          ·
            refine ⟨19143513577800802525709377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25524684770401070034279169 19143513577800802525709377)
            ·
              refine ⟨14357635183350601894282033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19143513577800802525709377 14357635183350601894282033)
              ·
                refine ⟨10768226387512951420711525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14357635183350601894282033 10768226387512951420711525)
                ·
                  refine ⟨2019042447658678391383411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10768226387512951420711525 2019042447658678391383411)
                  ·
                    refine ⟨3028563671488017587075117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2019042447658678391383411 3028563671488017587075117)
                    ·
                      refine ⟨1135711376808006595153169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3028563671488017587075117 1135711376808006595153169)
                      ·
                        rfl

theorem cell23_2211790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 4, 1, 3].length) (baseStart_2211790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2211790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2211790 prefixEnd_2211790 := by exact prefixLift 2211790
  have htrace : WordTrace (prefixWord ++ tailWord_2211790) baseStart_2211790 baseEnd_2211790 := by
    simpa [prefixWord, tailWord_2211790, baseEnd_2211790] using wordTrace_append hprefix tailTrace_2211790
  have hstable : (prefixWord ++ tailWord_2211790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211790).length < 2 ^ (prefixWord ++ tailWord_2211790).sum := by decide
  have hdescent : baseEnd_2211790 < baseStart_2211790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211807 : List Nat := [1, 1, 2, 3, 4, 1, 3, 2, 2, 1, 3]
def baseStart_2211807 : Nat := 118140960795 + 2211807 * 2 ^ 59
def prefixEnd_2211807 : Nat := 4983230072969 + 3 ^ 40 * 2211807 * 2
def baseEnd_2211807 : Nat := 1135720105979133028640591

theorem tailTrace_2211807 : CollatzResearch.WordTrace tailWord_2211807 prefixEnd_2211807 1135720105979133028640591 := by
  unfold tailWord_2211807
  simp only [CollatzResearch.WordTrace]
  refine ⟨80671228698008460406769675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53780819132005640271179783 80671228698008460406769675)
  ·
    refine ⟨121006843047012690610154513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80671228698008460406769675 121006843047012690610154513)
    ·
      refine ⟨90755132285259517957615885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121006843047012690610154513 90755132285259517957615885)
      ·
        refine ⟨34033174606972319234105957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90755132285259517957615885 34033174606972319234105957)
        ·
          refine ⟨6381220238807309856394867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34033174606972319234105957 6381220238807309856394867)
          ·
            refine ⟨9571830358210964784592301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6381220238807309856394867 9571830358210964784592301)
            ·
              refine ⟨3589436384329111794222113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9571830358210964784592301 3589436384329111794222113)
              ·
                refine ⟨2692077288246833845666585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3589436384329111794222113 2692077288246833845666585)
                ·
                  refine ⟨2019057966185125384249939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2692077288246833845666585 2019057966185125384249939)
                  ·
                    refine ⟨3028586949277688076374909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2019057966185125384249939 3028586949277688076374909)
                    ·
                      refine ⟨1135720105979133028640591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3028586949277688076374909 1135720105979133028640591)
                      ·
                        rfl

theorem cell23_2211807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 2, 2, 1, 3].length) (baseStart_2211807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2211807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2211807 prefixEnd_2211807 := by exact prefixLift 2211807
  have htrace : WordTrace (prefixWord ++ tailWord_2211807) baseStart_2211807 baseEnd_2211807 := by
    simpa [prefixWord, tailWord_2211807, baseEnd_2211807] using wordTrace_append hprefix tailTrace_2211807
  have hstable : (prefixWord ++ tailWord_2211807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211807).length < 2 ^ (prefixWord ++ tailWord_2211807).sum := by decide
  have hdescent : baseEnd_2211807 < baseStart_2211807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211847 : List Nat := [1, 1, 4, 3, 1, 2, 1, 2, 4, 2, 2]
def baseStart_2211847 : Nat := 118140960795 + 2211847 * 2 ^ 59
def prefixEnd_2211847 : Nat := 4983230072969 + 3 ^ 40 * 2211847 * 2
def baseEnd_2211847 : Nat := 1135740645205312872140407

theorem tailTrace_2211847 : CollatzResearch.WordTrace tailWord_2211847 prefixEnd_2211847 1135740645205312872140407 := by
  unfold tailWord_2211847
  simp only [CollatzResearch.WordTrace]
  refine ⟨80672687617863547238225795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53781791745242364825483863 80672687617863547238225795)
  ·
    refine ⟨121009031426795320857338693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80672687617863547238225795 121009031426795320857338693)
    ·
      refine ⟨22689193392524122660751005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121009031426795320857338693 22689193392524122660751005)
      ·
        refine ⟨8508447522196545997781627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22689193392524122660751005 8508447522196545997781627)
        ·
          refine ⟨12762671283294818996672441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8508447522196545997781627 12762671283294818996672441)
          ·
            refine ⟨9572003462471114247504331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12762671283294818996672441 9572003462471114247504331)
            ·
              refine ⟨14358005193706671371256497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9572003462471114247504331 14358005193706671371256497)
              ·
                refine ⟨10768503895280003528442373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14358005193706671371256497 10768503895280003528442373)
                ·
                  refine ⟨2019094480365000661582945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10768503895280003528442373 2019094480365000661582945)
                  ·
                    refine ⟨1514320860273750496187209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2019094480365000661582945 1514320860273750496187209)
                    ·
                      refine ⟨1135740645205312872140407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1514320860273750496187209 1135740645205312872140407)
                      ·
                        rfl

theorem cell23_2211847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_2211847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2211847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2211847 prefixEnd_2211847 := by exact prefixLift 2211847
  have htrace : WordTrace (prefixWord ++ tailWord_2211847) baseStart_2211847 baseEnd_2211847 := by
    simpa [prefixWord, tailWord_2211847, baseEnd_2211847] using wordTrace_append hprefix tailTrace_2211847
  have hstable : (prefixWord ++ tailWord_2211847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211847).length < 2 ^ (prefixWord ++ tailWord_2211847).sum := by decide
  have hdescent : baseEnd_2211847 < baseStart_2211847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211850 : List Nat := [3, 1, 2, 2, 4, 1, 1, 1, 2, 1, 5]
def baseStart_2211850 : Nat := 118140960795 + 2211850 * 2 ^ 59
def prefixEnd_2211850 : Nat := 4983230072969 + 3 ^ 40 * 2211850 * 2
def baseEnd_2211850 : Nat := 1135742185647276360402893

theorem tailTrace_2211850 : CollatzResearch.WordTrace tailWord_2211850 prefixEnd_2211850 1135742185647276360402893 := by
  unfold tailWord_2211850
  simp only [CollatzResearch.WordTrace]
  refine ⟨20168199259213169687646251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53781864691235119167056669 20168199259213169687646251)
  ·
    refine ⟨30252298888819754531469377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20168199259213169687646251 30252298888819754531469377)
    ·
      refine ⟨22689224166614815898602033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30252298888819754531469377 22689224166614815898602033)
      ·
        refine ⟨17016918124961111923951525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22689224166614815898602033 17016918124961111923951525)
        ·
          refine ⟨3190672148430208485740911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17016918124961111923951525 3190672148430208485740911)
          ·
            refine ⟨4786008222645312728611367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3190672148430208485740911 4786008222645312728611367)
            ·
              refine ⟨7179012333967969092917051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4786008222645312728611367 7179012333967969092917051)
              ·
                refine ⟨10768518500951953639375577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7179012333967969092917051 10768518500951953639375577)
                ·
                  refine ⟨8076388875713965229531683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10768518500951953639375577 8076388875713965229531683)
                  ·
                    refine ⟨12114583313570947844297525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8076388875713965229531683 12114583313570947844297525)
                    ·
                      refine ⟨1135742185647276360402893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12114583313570947844297525 1135742185647276360402893)
                      ·
                        rfl

theorem cell23_2211850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_2211850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2211850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2211850 prefixEnd_2211850 := by exact prefixLift 2211850
  have htrace : WordTrace (prefixWord ++ tailWord_2211850) baseStart_2211850 baseEnd_2211850 := by
    simpa [prefixWord, tailWord_2211850, baseEnd_2211850] using wordTrace_append hprefix tailTrace_2211850
  have hstable : (prefixWord ++ tailWord_2211850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211850).length < 2 ^ (prefixWord ++ tailWord_2211850).sum := by decide
  have hdescent : baseEnd_2211850 < baseStart_2211850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211900 : List Nat := [2, 2, 2, 2, 2, 1, 4, 1, 2, 5]
def baseStart_2211900 : Nat := 118140960795 + 2211900 * 2 ^ 59
def prefixEnd_2211900 : Nat := 4983230072969 + 3 ^ 40 * 2211900 * 2
def baseEnd_2211900 : Nat := 378589286560000388259221

theorem tailTrace_2211900 : CollatzResearch.WordTrace tailWord_2211900 prefixEnd_2211900 378589286560000388259221 := by
  unfold tailWord_2211900
  simp only [CollatzResearch.WordTrace]
  refine ⟨40337310343335768644952577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53783080457781024859936769 40337310343335768644952577)
  ·
    refine ⟨30252982757501826483714433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40337310343335768644952577 30252982757501826483714433)
    ·
      refine ⟨22689737068126369862785825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30252982757501826483714433 22689737068126369862785825)
      ·
        refine ⟨17017302801094777397089369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22689737068126369862785825 17017302801094777397089369)
        ·
          refine ⟨12762977100821083047817027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17017302801094777397089369 12762977100821083047817027)
          ·
            refine ⟨19144465651231624571725541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12762977100821083047817027 19144465651231624571725541)
            ·
              refine ⟨3589587309605929607198539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19144465651231624571725541 3589587309605929607198539)
              ·
                refine ⟨5384380964408894410797809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3589587309605929607198539 5384380964408894410797809)
                ·
                  refine ⟨4038285723306670808098357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5384380964408894410797809 4038285723306670808098357)
                  ·
                    refine ⟨378589286560000388259221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4038285723306670808098357 378589286560000388259221)
                    ·
                      rfl

theorem cell23_2211900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 2, 5].length) (baseStart_2211900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2211900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2211900 prefixEnd_2211900 := by exact prefixLift 2211900
  have htrace : WordTrace (prefixWord ++ tailWord_2211900) baseStart_2211900 baseEnd_2211900 := by
    simpa [prefixWord, tailWord_2211900, baseEnd_2211900] using wordTrace_append hprefix tailTrace_2211900
  have hstable : (prefixWord ++ tailWord_2211900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211900).length < 2 ^ (prefixWord ++ tailWord_2211900).sum := by decide
  have hdescent : baseEnd_2211900 < baseStart_2211900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211903 : List Nat := [1, 1, 2, 2, 3, 1, 2, 3, 1, 3, 4]
def baseStart_2211903 : Nat := 118140960795 + 2211903 * 2 ^ 59
def prefixEnd_2211903 : Nat := 4983230072969 + 3 ^ 40 * 2211903 * 2
def baseEnd_2211903 : Nat := 1135769400121964653040149

theorem tailTrace_2211903 : CollatzResearch.WordTrace tailWord_2211903 prefixEnd_2211903 1135769400121964653040149 := by
  unfold tailWord_2211903
  simp only [CollatzResearch.WordTrace]
  refine ⟨80674730105660668802264363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53783153403773779201509575 80674730105660668802264363)
  ·
    refine ⟨121012095158491003203396545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80674730105660668802264363 121012095158491003203396545)
    ·
      refine ⟨90759071368868252402547409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121012095158491003203396545 90759071368868252402547409)
      ·
        refine ⟨68069303526651189301910557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90759071368868252402547409 68069303526651189301910557)
        ·
          refine ⟨25525988822494195988216459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68069303526651189301910557 25525988822494195988216459)
          ·
            refine ⟨38288983233741293982324689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25525988822494195988216459 38288983233741293982324689)
            ·
              refine ⟨28716737425305970486743517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38288983233741293982324689 28716737425305970486743517)
              ·
                refine ⟨10768776534489738932528819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28716737425305970486743517 10768776534489738932528819)
                ·
                  refine ⟨16153164801734608398793229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10768776534489738932528819 16153164801734608398793229)
                  ·
                    refine ⟨6057436800650478149547461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16153164801734608398793229 6057436800650478149547461)
                    ·
                      refine ⟨1135769400121964653040149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6057436800650478149547461 1135769400121964653040149)
                      ·
                        rfl

theorem cell23_2211903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 3, 4].length) (baseStart_2211903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2211903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2211903 prefixEnd_2211903 := by exact prefixLift 2211903
  have htrace : WordTrace (prefixWord ++ tailWord_2211903) baseStart_2211903 baseEnd_2211903 := by
    simpa [prefixWord, tailWord_2211903, baseEnd_2211903] using wordTrace_append hprefix tailTrace_2211903
  have hstable : (prefixWord ++ tailWord_2211903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211903).length < 2 ^ (prefixWord ++ tailWord_2211903).sum := by decide
  have hdescent : baseEnd_2211903 < baseStart_2211903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211930 : List Nat := [3, 1, 1, 2, 1, 1, 4, 3, 3, 4]
def baseStart_2211930 : Nat := 118140960795 + 2211930 * 2 ^ 59
def prefixEnd_2211930 : Nat := 4983230072969 + 3 ^ 40 * 2211930 * 2
def baseEnd_2211930 : Nat := 378594421366545349134175

theorem tailTrace_2211930 : CollatzResearch.WordTrace tailWord_2211930 prefixEnd_2211930 378594421366545349134175 := by
  unfold tailWord_2211930
  simp only [CollatzResearch.WordTrace]
  refine ⟨20168928719140713103374311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53783809917708568275664829 20168928719140713103374311)
  ·
    refine ⟨30253393078711069655061467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20168928719140713103374311 30253393078711069655061467)
    ·
      refine ⟨45380089618066604482592201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30253393078711069655061467 45380089618066604482592201)
      ·
        refine ⟨34035067213549953361944151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45380089618066604482592201 34035067213549953361944151)
        ·
          refine ⟨51052600820324930042916227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34035067213549953361944151 51052600820324930042916227)
          ·
            refine ⟨76578901230487395064374341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51052600820324930042916227 76578901230487395064374341)
            ·
              refine ⟨14358543980716386574570189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76578901230487395064374341 14358543980716386574570189)
              ·
                refine ⟨5384453992768644965463821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14358543980716386574570189 5384453992768644965463821)
                ·
                  refine ⟨2019170247288241862048933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5384453992768644965463821 2019170247288241862048933)
                  ·
                    refine ⟨378594421366545349134175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2019170247288241862048933 378594421366545349134175)
                    ·
                      rfl

theorem cell23_2211930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 3, 4].length) (baseStart_2211930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2211930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2211930 prefixEnd_2211930 := by exact prefixLift 2211930
  have htrace : WordTrace (prefixWord ++ tailWord_2211930) baseStart_2211930 baseEnd_2211930 := by
    simpa [prefixWord, tailWord_2211930, baseEnd_2211930] using wordTrace_append hprefix tailTrace_2211930
  have hstable : (prefixWord ++ tailWord_2211930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211930).length < 2 ^ (prefixWord ++ tailWord_2211930).sum := by decide
  have hdescent : baseEnd_2211930 < baseStart_2211930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211940 : List Nat := [2, 3, 1, 1, 2, 1, 2, 2, 4, 2, 3]
def baseStart_2211940 : Nat := 118140960795 + 2211940 * 2 ^ 59
def prefixEnd_2211940 : Nat := 4983230072969 + 3 ^ 40 * 2211940 * 2
def baseEnd_2211940 : Nat := 1135788398906181008277479

theorem tailTrace_2211940 : CollatzResearch.WordTrace tailWord_2211940 prefixEnd_2211940 1135788398906181008277479 := by
  unfold tailWord_2211940
  simp only [CollatzResearch.WordTrace]
  refine ⟨40338039803263312060680637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53784053071017749414240849 40338039803263312060680637)
  ·
    refine ⟨15126764926223742022755239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40338039803263312060680637 15126764926223742022755239)
    ·
      refine ⟨22690147389335613034132859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15126764926223742022755239 22690147389335613034132859)
      ·
        refine ⟨34035221084003419551199289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22690147389335613034132859 34035221084003419551199289)
        ·
          refine ⟨25526415813002564663399467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34035221084003419551199289 25526415813002564663399467)
          ·
            refine ⟨38289623719503846995099201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25526415813002564663399467 38289623719503846995099201)
            ·
              refine ⟨28717217789627885246324401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38289623719503846995099201 28717217789627885246324401)
              ·
                refine ⟨21537913342220913934743301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28717217789627885246324401 21537913342220913934743301)
                ·
                  refine ⟨4038358751666421362764369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21537913342220913934743301 4038358751666421362764369)
                  ·
                    refine ⟨3028769063749816022073277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4038358751666421362764369 3028769063749816022073277)
                    ·
                      refine ⟨1135788398906181008277479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3028769063749816022073277 1135788398906181008277479)
                      ·
                        rfl

theorem cell23_2211940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 4, 2, 3].length) (baseStart_2211940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2211940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2211940 prefixEnd_2211940 := by exact prefixLift 2211940
  have htrace : WordTrace (prefixWord ++ tailWord_2211940) baseStart_2211940 baseEnd_2211940 := by
    simpa [prefixWord, tailWord_2211940, baseEnd_2211940] using wordTrace_append hprefix tailTrace_2211940
  have hstable : (prefixWord ++ tailWord_2211940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211940).length < 2 ^ (prefixWord ++ tailWord_2211940).sum := by decide
  have hdescent : baseEnd_2211940 < baseStart_2211940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211964 : List Nat := [2, 2, 2, 1, 1, 5, 2, 3, 1, 4]
def baseStart_2211964 : Nat := 118140960795 + 2211964 * 2 ^ 59
def prefixEnd_2211964 : Nat := 4983230072969 + 3 ^ 40 * 2211964 * 2
def baseEnd_2211964 : Nat := 378600240813962971459123

theorem tailTrace_2211964 : CollatzResearch.WordTrace tailWord_2211964 prefixEnd_2211964 378600240813962971459123 := by
  unfold tailWord_2211964
  simp only [CollatzResearch.WordTrace]
  refine ⟨40338477479219838110117473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53784636638959784146823297 40338477479219838110117473)
  ·
    refine ⟨30253858109414878582588105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40338477479219838110117473 30253858109414878582588105)
    ·
      refine ⟨22690393582061158936941079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30253858109414878582588105 22690393582061158936941079)
      ·
        refine ⟨34035590373091738405411619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22690393582061158936941079 34035590373091738405411619)
        ·
          refine ⟨51053385559637607608117429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34035590373091738405411619 51053385559637607608117429)
          ·
            refine ⟨4786254896216025713261009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51053385559637607608117429 4786254896216025713261009)
            ·
              refine ⟨3589691172162019284945757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4786254896216025713261009 3589691172162019284945757)
              ·
                refine ⟨1346134189560757231854659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3589691172162019284945757 1346134189560757231854659)
                ·
                  refine ⟨2019201284341135847781989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1346134189560757231854659 2019201284341135847781989)
                  ·
                    refine ⟨378600240813962971459123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2019201284341135847781989 378600240813962971459123)
                    ·
                      rfl

theorem cell23_2211964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 3, 1, 4].length) (baseStart_2211964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2211964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2211964 prefixEnd_2211964 := by exact prefixLift 2211964
  have htrace : WordTrace (prefixWord ++ tailWord_2211964) baseStart_2211964 baseEnd_2211964 := by
    simpa [prefixWord, tailWord_2211964, baseEnd_2211964] using wordTrace_append hprefix tailTrace_2211964
  have hstable : (prefixWord ++ tailWord_2211964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211964).length < 2 ^ (prefixWord ++ tailWord_2211964).sum := by decide
  have hdescent : baseEnd_2211964 < baseStart_2211964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211994 : List Nat := [3, 1, 1, 5, 2, 1, 3, 1, 6]
def baseStart_2211994 : Nat := 118140960795 + 2211994 * 2 ^ 59
def prefixEnd_2211994 : Nat := 4983230072969 + 3 ^ 40 * 2211994 * 2
def baseEnd_2211994 : Nat := 126201791873502644111359

theorem tailTrace_2211994 : CollatzResearch.WordTrace tailWord_2211994 prefixEnd_2211994 126201791873502644111359 := by
  unfold tailWord_2211994
  simp only [CollatzResearch.WordTrace]
  refine ⟨20169512287082747835956759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53785366098887327562551357 20169512287082747835956759)
  ·
    refine ⟨30254268430624121753935139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20169512287082747835956759 30254268430624121753935139)
    ·
      refine ⟨45381402645936182630902709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30254268430624121753935139 45381402645936182630902709)
      ·
        refine ⟨4254506498056517121647129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45381402645936182630902709 4254506498056517121647129)
        ·
          refine ⟨3190879873542387841235347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4254506498056517121647129 3190879873542387841235347)
          ·
            refine ⟨4786319810313581761853021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3190879873542387841235347 4786319810313581761853021)
            ·
              refine ⟨1794869928867593160694883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4786319810313581761853021 1794869928867593160694883)
              ·
                refine ⟨2692304893301389741042325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1794869928867593160694883 2692304893301389741042325)
                ·
                  refine ⟨126201791873502644111359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2692304893301389741042325 126201791873502644111359)
                  ·
                    rfl

theorem cell23_2211994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 1, 6].length) (baseStart_2211994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2211994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2211994 prefixEnd_2211994 := by exact prefixLift 2211994
  have htrace : WordTrace (prefixWord ++ tailWord_2211994) baseStart_2211994 baseEnd_2211994 := by
    simpa [prefixWord, tailWord_2211994, baseEnd_2211994] using wordTrace_append hprefix tailTrace_2211994
  have hstable : (prefixWord ++ tailWord_2211994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211994).length < 2 ^ (prefixWord ++ tailWord_2211994).sum := by decide
  have hdescent : baseEnd_2211994 < baseStart_2211994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2211997 : List Nat := [1, 4, 2, 1, 1, 3, 1, 2, 1, 5, 2]
def baseStart_2211997 : Nat := 118140960795 + 2211997 * 2 ^ 59
def prefixEnd_2211997 : Nat := 4983230072969 + 3 ^ 40 * 2211997 * 2
def baseEnd_2211997 : Nat := 1135817667303487285264717

theorem tailTrace_2211997 : CollatzResearch.WordTrace tailWord_2211997 prefixEnd_2211997 1135817667303487285264717 := by
  unfold tailWord_2211997
  simp only [CollatzResearch.WordTrace]
  refine ⟨80678158567320122856186245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53785439044880081904124163 80678158567320122856186245)
  ·
    refine ⟨15127154731372523035534921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80678158567320122856186245 15127154731372523035534921)
    ·
      refine ⟨11345366048529392276651191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15127154731372523035534921 11345366048529392276651191)
      ·
        refine ⟨17018049072794088414976787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11345366048529392276651191 17018049072794088414976787)
        ·
          refine ⟨25527073609191132622465181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17018049072794088414976787 25527073609191132622465181)
          ·
            refine ⟨9572652603446674733424443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25527073609191132622465181 9572652603446674733424443)
            ·
              refine ⟨14358978905170012100136665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9572652603446674733424443 14358978905170012100136665)
              ·
                refine ⟨10769234178877509075102499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14358978905170012100136665 10769234178877509075102499)
                ·
                  refine ⟨16153851268316263612653749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10769234178877509075102499 16153851268316263612653749)
                  ·
                    refine ⟨1514423556404649713686289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16153851268316263612653749 1514423556404649713686289)
                    ·
                      refine ⟨1135817667303487285264717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1514423556404649713686289 1135817667303487285264717)
                      ·
                        rfl

theorem cell23_2211997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 5, 2].length) (baseStart_2211997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2211997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2211997 prefixEnd_2211997 := by exact prefixLift 2211997
  have htrace : WordTrace (prefixWord ++ tailWord_2211997) baseStart_2211997 baseEnd_2211997 := by
    simpa [prefixWord, tailWord_2211997, baseEnd_2211997] using wordTrace_append hprefix tailTrace_2211997
  have hstable : (prefixWord ++ tailWord_2211997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2211997).length < 2 ^ (prefixWord ++ tailWord_2211997).sum := by decide
  have hdescent : baseEnd_2211997 < baseStart_2211997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2211997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212050 : List Nat := [3, 2, 2, 2, 1, 2, 1, 10]
def baseStart_2212050 : Nat := 118140960795 + 2212050 * 2 ^ 59
def prefixEnd_2212050 : Nat := 4983230072969 + 3 ^ 40 * 2212050 * 2
def baseEnd_2212050 : Nat := 42068328954747243625999

theorem tailTrace_2212050 : CollatzResearch.WordTrace tailWord_2212050 prefixEnd_2212050 42068328954747243625999 := by
  unfold tailWord_2212050
  simp only [CollatzResearch.WordTrace]
  refine ⟨20170022909032028226966401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53786727757418741938577069 20170022909032028226966401)
  ·
    refine ⟨15127517181774021170224801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20170022909032028226966401 15127517181774021170224801)
    ·
      refine ⟨11345637886330515877668601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15127517181774021170224801 11345637886330515877668601)
      ·
        refine ⟨8509228414747886908251451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11345637886330515877668601 8509228414747886908251451)
        ·
          refine ⟨12763842622121830362377177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8509228414747886908251451 12763842622121830362377177)
          ·
            refine ⟨9572881966591372771782883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12763842622121830362377177 9572881966591372771782883)
            ·
              refine ⟨14359322949887059157674325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9572881966591372771782883 14359322949887059157674325)
              ·
                refine ⟨42068328954747243625999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 14359322949887059157674325 42068328954747243625999)
                ·
                  rfl

theorem cell23_2212050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 10].length) (baseStart_2212050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2212050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2212050 prefixEnd_2212050 := by exact prefixLift 2212050
  have htrace : WordTrace (prefixWord ++ tailWord_2212050) baseStart_2212050 baseEnd_2212050 := by
    simpa [prefixWord, tailWord_2212050, baseEnd_2212050] using wordTrace_append hprefix tailTrace_2212050
  have hstable : (prefixWord ++ tailWord_2212050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212050).length < 2 ^ (prefixWord ++ tailWord_2212050).sum := by decide
  have hdescent : baseEnd_2212050 < baseStart_2212050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212061 : List Nat := [1, 4, 3, 2, 1, 3, 1, 2, 1, 1, 4]
def baseStart_2212061 : Nat := 118140960795 + 2212061 * 2 ^ 59
def prefixEnd_2212061 : Nat := 4983230072969 + 3 ^ 40 * 2212061 * 2
def baseEnd_2212061 : Nat := 1135850530065375034864423

theorem tailTrace_2212061 : CollatzResearch.WordTrace tailWord_2212061 prefixEnd_2212061 1135850530065375034864423 := by
  unfold tailWord_2212061
  simp only [CollatzResearch.WordTrace]
  refine ⟨80680492839088261786516037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53786995226058841191010691 80680492839088261786516037)
  ·
    refine ⟨15127592407329049084971757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80680492839088261786516037 15127592407329049084971757)
    ·
      refine ⟨5672847152748393406864409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15127592407329049084971757 5672847152748393406864409)
      ·
        refine ⟨4254635364561295055148307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5672847152748393406864409 4254635364561295055148307)
        ·
          refine ⟨6381953046841942582722461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4254635364561295055148307 6381953046841942582722461)
          ·
            refine ⟨2393232392565728468520923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6381953046841942582722461 2393232392565728468520923)
            ·
              refine ⟨3589848588848592702781385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2393232392565728468520923 3589848588848592702781385)
              ·
                refine ⟨2692386441636444527086039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3589848588848592702781385 2692386441636444527086039)
                ·
                  refine ⟨4038579662454666790629059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2692386441636444527086039 4038579662454666790629059)
                  ·
                    refine ⟨6057869493682000185943589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4038579662454666790629059 6057869493682000185943589)
                    ·
                      refine ⟨1135850530065375034864423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6057869493682000185943589 1135850530065375034864423)
                      ·
                        rfl

theorem cell23_2212061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_2212061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2212061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2212061 prefixEnd_2212061 := by exact prefixLift 2212061
  have htrace : WordTrace (prefixWord ++ tailWord_2212061) baseStart_2212061 baseEnd_2212061 := by
    simpa [prefixWord, tailWord_2212061, baseEnd_2212061] using wordTrace_append hprefix tailTrace_2212061
  have hstable : (prefixWord ++ tailWord_2212061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212061).length < 2 ^ (prefixWord ++ tailWord_2212061).sum := by decide
  have hdescent : baseEnd_2212061 < baseStart_2212061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212087 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 7, 3, 2]
def baseStart_2212087 : Nat := 118140960795 + 2212087 * 2 ^ 59
def prefixEnd_2212087 : Nat := 4983230072969 + 3 ^ 40 * 2212087 * 2
def baseEnd_2212087 : Nat := 1135863880562391933139303

theorem tailTrace_2212087 : CollatzResearch.WordTrace tailWord_2212087 prefixEnd_2212087 1135863880562391933139303 := by
  unfold tailWord_2212087
  simp only [CollatzResearch.WordTrace]
  refine ⟨80681441136994068226962515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53787627424662712151308343 80681441136994068226962515)
  ·
    refine ⟨121022161705491102340443773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80681441136994068226962515 121022161705491102340443773)
    ·
      refine ⟨45383310639559163377666415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121022161705491102340443773 45383310639559163377666415)
      ·
        refine ⟨68074965959338745066499623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45383310639559163377666415 68074965959338745066499623)
        ·
          refine ⟨102112448939008117599749435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68074965959338745066499623 102112448939008117599749435)
          ·
            refine ⟨153168673408512176399624153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102112448939008117599749435 153168673408512176399624153)
            ·
              refine ⟨114876505056384132299718115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153168673408512176399624153 114876505056384132299718115)
              ·
                refine ⟨172314757584576198449577173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114876505056384132299718115 172314757584576198449577173)
                ·
                  refine ⟨4038627130888504651161965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 172314757584576198449577173 4038627130888504651161965)
                  ·
                    refine ⟨1514485174083189244185737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4038627130888504651161965 1514485174083189244185737)
                    ·
                      refine ⟨1135863880562391933139303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1514485174083189244185737 1135863880562391933139303)
                      ·
                        rfl

theorem cell23_2212087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 7, 3, 2].length) (baseStart_2212087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2212087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2212087 prefixEnd_2212087 := by exact prefixLift 2212087
  have htrace : WordTrace (prefixWord ++ tailWord_2212087) baseStart_2212087 baseEnd_2212087 := by
    simpa [prefixWord, tailWord_2212087, baseEnd_2212087] using wordTrace_append hprefix tailTrace_2212087
  have hstable : (prefixWord ++ tailWord_2212087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212087).length < 2 ^ (prefixWord ++ tailWord_2212087).sum := by decide
  have hdescent : baseEnd_2212087 < baseStart_2212087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212104 : List Nat := [2, 1, 3, 2, 3, 1, 1, 2, 3, 3, 2]
def baseStart_2212104 : Nat := 118140960795 + 2212104 * 2 ^ 59
def prefixEnd_2212104 : Nat := 4983230072969 + 3 ^ 40 * 2212104 * 2
def baseEnd_2212104 : Nat := 1135872609733518366626725

theorem tailTrace_2212104 : CollatzResearch.WordTrace tailWord_2212104 prefixEnd_2212104 1135872609733518366626725 := by
  unfold tailWord_2212104
  simp only [CollatzResearch.WordTrace]
  refine ⟨40341030588966240065165683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53788040785288320086887577 40341030588966240065165683)
  ·
    refine ⟨60511545883449360097748525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40341030588966240065165683 60511545883449360097748525)
    ·
      refine ⟨22691829706293510036655697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60511545883449360097748525 22691829706293510036655697)
      ·
        refine ⟨17018872279720132527491773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22691829706293510036655697 17018872279720132527491773)
        ·
          refine ⟨6382077104895049697809415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17018872279720132527491773 6382077104895049697809415)
          ·
            refine ⟨9573115657342574546714123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6382077104895049697809415 9573115657342574546714123)
            ·
              refine ⟨14359673486013861820071185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9573115657342574546714123 14359673486013861820071185)
              ·
                refine ⟨10769755114510396365053389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14359673486013861820071185 10769755114510396365053389)
                ·
                  refine ⟨4038658167941398636895021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10769755114510396365053389 4038658167941398636895021)
                  ·
                    refine ⟨1514496812978024488835633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4038658167941398636895021 1514496812978024488835633)
                    ·
                      refine ⟨1135872609733518366626725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1514496812978024488835633 1135872609733518366626725)
                      ·
                        rfl

theorem cell23_2212104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 3, 3, 2].length) (baseStart_2212104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2212104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2212104 prefixEnd_2212104 := by exact prefixLift 2212104
  have htrace : WordTrace (prefixWord ++ tailWord_2212104) baseStart_2212104 baseEnd_2212104 := by
    simpa [prefixWord, tailWord_2212104, baseEnd_2212104] using wordTrace_append hprefix tailTrace_2212104
  have hstable : (prefixWord ++ tailWord_2212104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212104).length < 2 ^ (prefixWord ++ tailWord_2212104).sum := by decide
  have hdescent : baseEnd_2212104 < baseStart_2212104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212138 : List Nat := [3, 1, 4, 2, 2, 1, 1, 3, 1, 3, 2]
def baseStart_2212138 : Nat := 118140960795 + 2212138 * 2 ^ 59
def prefixEnd_2212138 : Nat := 4983230072969 + 3 ^ 40 * 2212138 * 2
def baseEnd_2212138 : Nat := 1135890068075771233601569

theorem tailTrace_2212138 : CollatzResearch.WordTrace tailWord_2212138 prefixEnd_2212138 1135890068075771233601569 := by
  unfold tailWord_2212138
  simp only [CollatzResearch.WordTrace]
  refine ⟨20170825314952325984267267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53788867506539535958046045 20170825314952325984267267)
  ·
    refine ⟨30256237972428488976400901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20170825314952325984267267 30256237972428488976400901)
    ·
      refine ⟨5673044619830341683075169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30256237972428488976400901 5673044619830341683075169)
      ·
        refine ⟨4254783464872756262306377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5673044619830341683075169 4254783464872756262306377)
        ·
          refine ⟨3191087598654567196729783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4254783464872756262306377 3191087598654567196729783)
          ·
            refine ⟨4786631397981850795094675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3191087598654567196729783 4786631397981850795094675)
            ·
              refine ⟨7179947096972776192642013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4786631397981850795094675 7179947096972776192642013)
              ·
                refine ⟨2692480161364791072240755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7179947096972776192642013 2692480161364791072240755)
                ·
                  refine ⟨4038720242047186608361133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2692480161364791072240755 4038720242047186608361133)
                  ·
                    refine ⟨1514520090767694978135425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4038720242047186608361133 1514520090767694978135425)
                    ·
                      refine ⟨1135890068075771233601569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1514520090767694978135425 1135890068075771233601569)
                      ·
                        rfl

theorem cell23_2212138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_2212138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2212138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2212138 prefixEnd_2212138 := by exact prefixLift 2212138
  have htrace : WordTrace (prefixWord ++ tailWord_2212138) baseStart_2212138 baseEnd_2212138 := by
    simpa [prefixWord, tailWord_2212138, baseEnd_2212138] using wordTrace_append hprefix tailTrace_2212138
  have hstable : (prefixWord ++ tailWord_2212138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212138).length < 2 ^ (prefixWord ++ tailWord_2212138).sum := by decide
  have hdescent : baseEnd_2212138 < baseStart_2212138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212167 : List Nat := [1, 1, 4, 1, 2, 2, 1, 3, 2, 3, 3]
def baseStart_2212167 : Nat := 118140960795 + 2212167 * 2 ^ 59
def prefixEnd_2212167 : Nat := 4983230072969 + 3 ^ 40 * 2212167 * 2
def baseEnd_2212167 : Nat := 1135904959014751620138935

theorem tailTrace_2212167 : CollatzResearch.WordTrace tailWord_2212167 prefixEnd_2212167 1135904959014751620138935 := by
  unfold tailWord_2212167
  simp only [CollatzResearch.WordTrace]
  refine ⟨80684358976704241889874755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53789572651136161259916503 80684358976704241889874755)
  ·
    refine ⟨121026538465056362834812133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80684358976704241889874755 121026538465056362834812133)
    ·
      refine ⟨22692475962198068031527275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121026538465056362834812133 22692475962198068031527275)
      ·
        refine ⟨34038713943297102047290913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22692475962198068031527275 34038713943297102047290913)
        ·
          refine ⟨25529035457472826535468185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34038713943297102047290913 25529035457472826535468185)
          ·
            refine ⟨19146776593104619901601139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25529035457472826535468185 19146776593104619901601139)
            ·
              refine ⟨28720164889656929852401709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19146776593104619901601139 28720164889656929852401709)
              ·
                refine ⟨10770061833621348694650641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28720164889656929852401709 10770061833621348694650641)
                ·
                  refine ⟨8077546375216011520987981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10770061833621348694650641 8077546375216011520987981)
                  ·
                    refine ⟨3029079890706004320370493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8077546375216011520987981 3029079890706004320370493)
                    ·
                      refine ⟨1135904959014751620138935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3029079890706004320370493 1135904959014751620138935)
                      ·
                        rfl

theorem cell23_2212167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 3, 3].length) (baseStart_2212167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2212167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2212167 prefixEnd_2212167 := by exact prefixLift 2212167
  have htrace : WordTrace (prefixWord ++ tailWord_2212167) baseStart_2212167 baseEnd_2212167 := by
    simpa [prefixWord, tailWord_2212167, baseEnd_2212167] using wordTrace_append hprefix tailTrace_2212167
  have hstable : (prefixWord ++ tailWord_2212167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212167).length < 2 ^ (prefixWord ++ tailWord_2212167).sum := by decide
  have hdescent : baseEnd_2212167 < baseStart_2212167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212204 : List Nat := [2, 2, 1, 1, 6, 1, 1, 2, 2, 5]
def baseStart_2212204 : Nat := 118140960795 + 2212204 * 2 ^ 59
def prefixEnd_2212204 : Nat := 4983230072969 + 3 ^ 40 * 2212204 * 2
def baseEnd_2212204 : Nat := 378641319266322658458755

theorem tailTrace_2212204 : CollatzResearch.WordTrace tailWord_2212204 prefixEnd_2212204 378641319266322658458755 := by
  unfold tailWord_2212204
  simp only [CollatzResearch.WordTrace]
  refine ⟨40342854238785098604485833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53790472318380131472647777 40342854238785098604485833)
  ·
    refine ⟨30257140679088823953364375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40342854238785098604485833 30257140679088823953364375)
    ·
      refine ⟨45385711018633235930046563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30257140679088823953364375 45385711018633235930046563)
      ·
        refine ⟨68078566527949853895069845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45385711018633235930046563 68078566527949853895069845)
        ·
          refine ⟨3191182805997649401331399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 68078566527949853895069845 3191182805997649401331399)
          ·
            refine ⟨4786774208996474101997099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3191182805997649401331399 4786774208996474101997099)
            ·
              refine ⟨7180161313494711152995649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4786774208996474101997099 7180161313494711152995649)
              ·
                refine ⟨5385120985121033364746737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7180161313494711152995649 5385120985121033364746737)
                ·
                  refine ⟨4038840738840775023560053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5385120985121033364746737 4038840738840775023560053)
                  ·
                    refine ⟨378641319266322658458755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4038840738840775023560053 378641319266322658458755)
                    ·
                      rfl

theorem cell23_2212204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 5].length) (baseStart_2212204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2212204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2212204 prefixEnd_2212204 := by exact prefixLift 2212204
  have htrace : WordTrace (prefixWord ++ tailWord_2212204) baseStart_2212204 baseEnd_2212204 := by
    simpa [prefixWord, tailWord_2212204, baseEnd_2212204] using wordTrace_append hprefix tailTrace_2212204
  have hstable : (prefixWord ++ tailWord_2212204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212204).length < 2 ^ (prefixWord ++ tailWord_2212204).sum := by decide
  have hdescent : baseEnd_2212204 < baseStart_2212204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212334 : List Nat := [4, 1, 2, 1, 2, 2, 1, 1, 3, 1, 5]
def baseStart_2212334 : Nat := 118140960795 + 2212334 * 2 ^ 59
def prefixEnd_2212334 : Nat := 4983230072969 + 3 ^ 40 * 2212334 * 2
def baseEnd_2212334 : Nat := 1135990710284052466750667

theorem tailTrace_2212334 : CollatzResearch.WordTrace tailWord_2212334 prefixEnd_2212334 1135990710284052466750667 := by
  unfold tailWord_2212334
  simp only [CollatzResearch.WordTrace]
  refine ⟨10086306245887403676400507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53793633311399486274136037 10086306245887403676400507)
  ·
    refine ⟨15129459368831105514600761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10086306245887403676400507 15129459368831105514600761)
    ·
      refine ⟨11347094526623329135950571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15129459368831105514600761 11347094526623329135950571)
      ·
        refine ⟨17020641789934993703925857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11347094526623329135950571 17020641789934993703925857)
        ·
          refine ⟨12765481342451245277944393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17020641789934993703925857 12765481342451245277944393)
          ·
            refine ⟨9574111006838433958458295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12765481342451245277944393 9574111006838433958458295)
            ·
              refine ⟨14361166510257650937687443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9574111006838433958458295 14361166510257650937687443)
              ·
                refine ⟨21541749765386476406531165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14361166510257650937687443 21541749765386476406531165)
                ·
                  refine ⟨8078156162019928652449187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21541749765386476406531165 8078156162019928652449187)
                  ·
                    refine ⟨12117234243029892978673781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8078156162019928652449187 12117234243029892978673781)
                    ·
                      refine ⟨1135990710284052466750667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12117234243029892978673781 1135990710284052466750667)
                      ·
                        rfl

theorem cell23_2212334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_2212334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2212334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2212334 prefixEnd_2212334 := by exact prefixLift 2212334
  have htrace : WordTrace (prefixWord ++ tailWord_2212334) baseStart_2212334 baseEnd_2212334 := by
    simpa [prefixWord, tailWord_2212334, baseEnd_2212334] using wordTrace_append hprefix tailTrace_2212334
  have hstable : (prefixWord ++ tailWord_2212334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212334).length < 2 ^ (prefixWord ++ tailWord_2212334).sum := by decide
  have hdescent : baseEnd_2212334 < baseStart_2212334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212337 : List Nat := [1, 2, 2, 2, 3, 1, 2, 10]
def baseStart_2212337 : Nat := 118140960795 + 2212337 * 2 ^ 59
def prefixEnd_2212337 : Nat := 4983230072969 + 3 ^ 40 * 2212337 * 2
def baseEnd_2212337 : Nat := 42073787063926516852339

theorem tailTrace_2212337 : CollatzResearch.WordTrace tailWord_2212337 prefixEnd_2212337 42073787063926516852339 := by
  unfold tailWord_2212337
  simp only [CollatzResearch.WordTrace]
  refine ⟨80690559386088360923563265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53793706257392240615708843 80690559386088360923563265)
  ·
    refine ⟨60517919539566270692672449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80690559386088360923563265 60517919539566270692672449)
    ·
      refine ⟨45388439654674703019504337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60517919539566270692672449 45388439654674703019504337)
      ·
        refine ⟨34041329741006027264628253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45388439654674703019504337 34041329741006027264628253)
        ·
          refine ⟨12765498652877260224235595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34041329741006027264628253 12765498652877260224235595)
          ·
            refine ⟨19148247979315890336353393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12765498652877260224235595 19148247979315890336353393)
            ·
              refine ⟨14361185984486917752265045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19148247979315890336353393 14361185984486917752265045)
              ·
                refine ⟨42073787063926516852339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 14361185984486917752265045 42073787063926516852339)
                ·
                  rfl

theorem cell23_2212337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 10].length) (baseStart_2212337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2212337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2212337 prefixEnd_2212337 := by exact prefixLift 2212337
  have htrace : WordTrace (prefixWord ++ tailWord_2212337) baseStart_2212337 baseEnd_2212337 := by
    simpa [prefixWord, tailWord_2212337, baseEnd_2212337] using wordTrace_append hprefix tailTrace_2212337
  have hstable : (prefixWord ++ tailWord_2212337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212337).length < 2 ^ (prefixWord ++ tailWord_2212337).sum := by decide
  have hdescent : baseEnd_2212337 < baseStart_2212337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212351 : List Nat := [1, 1, 2, 2, 1, 2, 6, 2, 1, 2, 3]
def baseStart_2212351 : Nat := 118140960795 + 2212351 * 2 ^ 59
def prefixEnd_2212351 : Nat := 4983230072969 + 3 ^ 40 * 2212351 * 2
def baseEnd_2212351 : Nat := 1135999439455178900238089

theorem tailTrace_2212351 : CollatzResearch.WordTrace tailWord_2212351 prefixEnd_2212351 1135999439455178900238089 := by
  unfold tailWord_2212351
  simp only [CollatzResearch.WordTrace]
  refine ⟨80691070008037641314572907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53794046672025094209715271 80691070008037641314572907)
  ·
    refine ⟨121036605012056461971859361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80691070008037641314572907 121036605012056461971859361)
    ·
      refine ⟨90777453759042346478894521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121036605012056461971859361 90777453759042346478894521)
      ·
        refine ⟨68083090319281759859170891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90777453759042346478894521 68083090319281759859170891)
        ·
          refine ⟨102124635478922639788756337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68083090319281759859170891 102124635478922639788756337)
          ·
            refine ⟨76593476609191979841567253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102124635478922639788756337 76593476609191979841567253)
            ·
              refine ⟨3590319216055874055073465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 76593476609191979841567253 3590319216055874055073465)
              ·
                refine ⟨2692739412041905541305099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3590319216055874055073465 2692739412041905541305099)
                ·
                  refine ⟨4039109118062858311957649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2692739412041905541305099 4039109118062858311957649)
                  ·
                    refine ⟨3029331838547143733968237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4039109118062858311957649 3029331838547143733968237)
                    ·
                      refine ⟨1135999439455178900238089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3029331838547143733968237 1135999439455178900238089)
                      ·
                        rfl

theorem cell23_2212351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 2, 1, 2, 3].length) (baseStart_2212351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2212351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2212351 prefixEnd_2212351 := by exact prefixLift 2212351
  have htrace : WordTrace (prefixWord ++ tailWord_2212351) baseStart_2212351 baseEnd_2212351 := by
    simpa [prefixWord, tailWord_2212351, baseEnd_2212351] using wordTrace_append hprefix tailTrace_2212351
  have hstable : (prefixWord ++ tailWord_2212351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212351).length < 2 ^ (prefixWord ++ tailWord_2212351).sum := by decide
  have hdescent : baseEnd_2212351 < baseStart_2212351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212365 : List Nat := [1, 7, 1, 1, 1, 1, 2, 3, 1, 1, 4]
def baseStart_2212365 : Nat := 118140960795 + 2212365 * 2 ^ 59
def prefixEnd_2212365 : Nat := 4983230072969 + 3 ^ 40 * 2212365 * 2
def baseEnd_2212365 : Nat := 1136006628184341845463025

theorem tailTrace_2212365 : CollatzResearch.WordTrace tailWord_2212365 prefixEnd_2212365 1136006628184341845463025 := by
  unfold tailWord_2212365
  simp only [CollatzResearch.WordTrace]
  refine ⟨80691580629986921705582549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53794387086657947803721699 80691580629986921705582549)
  ·
    refine ⟨1891208921015318477474591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 80691580629986921705582549 1891208921015318477474591)
    ·
      refine ⟨2836813381522977716211887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1891208921015318477474591 2836813381522977716211887)
      ·
        refine ⟨4255220072284466574317831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2836813381522977716211887 4255220072284466574317831)
        ·
          refine ⟨6382830108426699861476747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4255220072284466574317831 6382830108426699861476747)
          ·
            refine ⟨9574245162640049792215121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6382830108426699861476747 9574245162640049792215121)
            ·
              refine ⟨7180683871980037344161341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9574245162640049792215121 7180683871980037344161341)
              ·
                refine ⟨2692756451992514004060503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7180683871980037344161341 2692756451992514004060503)
                ·
                  refine ⟨4039134677988771006090755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2692756451992514004060503 4039134677988771006090755)
                  ·
                    refine ⟨6058702016983156509136133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4039134677988771006090755 6058702016983156509136133)
                    ·
                      refine ⟨1136006628184341845463025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6058702016983156509136133 1136006628184341845463025)
                      ·
                        rfl

theorem cell23_2212365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_2212365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2212365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2212365 prefixEnd_2212365 := by exact prefixLift 2212365
  have htrace : WordTrace (prefixWord ++ tailWord_2212365) baseStart_2212365 baseEnd_2212365 := by
    simpa [prefixWord, tailWord_2212365, baseEnd_2212365] using wordTrace_append hprefix tailTrace_2212365
  have hstable : (prefixWord ++ tailWord_2212365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212365).length < 2 ^ (prefixWord ++ tailWord_2212365).sum := by decide
  have hdescent : baseEnd_2212365 < baseStart_2212365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212421 : List Nat := [1, 3, 1, 1, 1, 5, 1, 1, 3, 4, 2]
def baseStart_2212421 : Nat := 118140960795 + 2212421 * 2 ^ 59
def prefixEnd_2212421 : Nat := 4983230072969 + 3 ^ 40 * 2212421 * 2
def baseEnd_2212421 : Nat := 1136035383100993626362767

theorem tailTrace_2212421 : CollatzResearch.WordTrace tailWord_2212421 prefixEnd_2212421 1136035383100993626362767 := by
  unfold tailWord_2212421
  simp only [CollatzResearch.WordTrace]
  refine ⟨80693623117784043269621117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53795748745189362179747411 80693623117784043269621117)
  ·
    refine ⟨30260108669169016226107919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80693623117784043269621117 30260108669169016226107919)
    ·
      refine ⟨45390163003753524339161879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30260108669169016226107919 45390163003753524339161879)
      ·
        refine ⟨68085244505630286508742819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45390163003753524339161879 68085244505630286508742819)
        ·
          refine ⟨102127866758445429763114229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68085244505630286508742819 102127866758445429763114229)
          ·
            refine ⟨9574487508604259040291959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 102127866758445429763114229 9574487508604259040291959)
            ·
              refine ⟨14361731262906388560437939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9574487508604259040291959 14361731262906388560437939)
              ·
                refine ⟨21542596894359582840656909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14361731262906388560437939 21542596894359582840656909)
                ·
                  refine ⟨8078473835384843565246341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21542596894359582840656909 8078473835384843565246341)
                  ·
                    refine ⟨1514713844134658168483689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8078473835384843565246341 1514713844134658168483689)
                    ·
                      refine ⟨1136035383100993626362767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1514713844134658168483689 1136035383100993626362767)
                      ·
                        rfl

theorem cell23_2212421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 4, 2].length) (baseStart_2212421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2212421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2212421 prefixEnd_2212421 := by exact prefixLift 2212421
  have htrace : WordTrace (prefixWord ++ tailWord_2212421) baseStart_2212421 baseEnd_2212421 := by
    simpa [prefixWord, tailWord_2212421, baseEnd_2212421] using wordTrace_append hprefix tailTrace_2212421
  have hstable : (prefixWord ++ tailWord_2212421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212421).length < 2 ^ (prefixWord ++ tailWord_2212421).sum := by decide
  have hdescent : baseEnd_2212421 < baseStart_2212421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212424 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 4, 4, 3]
def baseStart_2212424 : Nat := 118140960795 + 2212424 * 2 ^ 59
def prefixEnd_2212424 : Nat := 4983230072969 + 3 ^ 40 * 2212424 * 2
def baseEnd_2212424 : Nat := 1136036923542957114625253

theorem tailTrace_2212424 : CollatzResearch.WordTrace tailWord_2212424 prefixEnd_2212424 1136036923542957114625253 := by
  unfold tailWord_2212424
  simp only [CollatzResearch.WordTrace]
  refine ⟨40346866268386587390990163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53795821691182116521320217 40346866268386587390990163)
  ·
    refine ⟨60520299402579881086485245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40346866268386587390990163 60520299402579881086485245)
    ·
      refine ⟨22695112275967455407431967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60520299402579881086485245 22695112275967455407431967)
      ·
        refine ⟨34042668413951183111147951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22695112275967455407431967 34042668413951183111147951)
        ·
          refine ⟨51064002620926774666721927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34042668413951183111147951 51064002620926774666721927)
          ·
            refine ⟨76596003931390162000082891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51064002620926774666721927 76596003931390162000082891)
            ·
              refine ⟨114894005897085243000124337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76596003931390162000082891 114894005897085243000124337)
              ·
                refine ⟨86170504422813932250093253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114894005897085243000124337 86170504422813932250093253)
                ·
                  refine ⟨16156969579277612296892485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 86170504422813932250093253 16156969579277612296892485)
                  ·
                    refine ⟨3029431796114552305667341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16156969579277612296892485 3029431796114552305667341)
                    ·
                      refine ⟨1136036923542957114625253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3029431796114552305667341 1136036923542957114625253)
                      ·
                        rfl

theorem cell23_2212424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 4, 4, 3].length) (baseStart_2212424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2212424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2212424 prefixEnd_2212424 := by exact prefixLift 2212424
  have htrace : WordTrace (prefixWord ++ tailWord_2212424) baseStart_2212424 baseEnd_2212424 := by
    simpa [prefixWord, tailWord_2212424, baseEnd_2212424] using wordTrace_append hprefix tailTrace_2212424
  have hstable : (prefixWord ++ tailWord_2212424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212424).length < 2 ^ (prefixWord ++ tailWord_2212424).sum := by decide
  have hdescent : baseEnd_2212424 < baseStart_2212424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212461 : List Nat := [1, 5, 1, 1, 3, 2, 1, 2, 7]
def baseStart_2212461 : Nat := 118140960795 + 2212461 * 2 ^ 59
def prefixEnd_2212461 : Nat := 4983230072969 + 3 ^ 40 * 2212461 * 2
def baseEnd_2212461 : Nat := 126228435814130385540287

theorem tailTrace_2212461 : CollatzResearch.WordTrace tailWord_2212461 prefixEnd_2212461 126228435814130385540287 := by
  unfold tailWord_2212461
  simp only [CollatzResearch.WordTrace]
  refine ⟨80695082037639130101077237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53796721358426086734051491 80695082037639130101077237)
  ·
    refine ⟨7565163941028668446975991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80695082037639130101077237 7565163941028668446975991)
    ·
      refine ⟨11347745911543002670463987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7565163941028668446975991 11347745911543002670463987)
      ·
        refine ⟨17021618867314504005695981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11347745911543002670463987 17021618867314504005695981)
        ·
          refine ⟨6383107075242939002135993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17021618867314504005695981 6383107075242939002135993)
          ·
            refine ⟨4787330306432204251601995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6383107075242939002135993 4787330306432204251601995)
            ·
              refine ⟨7180995459648306377402993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4787330306432204251601995 7180995459648306377402993)
              ·
                refine ⟨5385746594736229783052245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7180995459648306377402993 5385746594736229783052245)
                ·
                  refine ⟨126228435814130385540287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5385746594736229783052245 126228435814130385540287)
                  ·
                    rfl

theorem cell23_2212461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 7].length) (baseStart_2212461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2212461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2212461 prefixEnd_2212461 := by exact prefixLift 2212461
  have htrace : WordTrace (prefixWord ++ tailWord_2212461) baseStart_2212461 baseEnd_2212461 := by
    simpa [prefixWord, tailWord_2212461, baseEnd_2212461] using wordTrace_append hprefix tailTrace_2212461
  have hstable : (prefixWord ++ tailWord_2212461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212461).length < 2 ^ (prefixWord ++ tailWord_2212461).sum := by decide
  have hdescent : baseEnd_2212461 < baseStart_2212461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212531 : List Nat := [1, 1, 1, 2, 3, 4, 2, 1, 1, 4, 3]
def baseStart_2212531 : Nat := 118140960795 + 2212531 * 2 ^ 59
def prefixEnd_2212531 : Nat := 4983230072969 + 3 ^ 40 * 2212531 * 2
def baseEnd_2212531 : Nat := 1136091865972988195987261

theorem tailTrace_2212531 : CollatzResearch.WordTrace tailWord_2212531 prefixEnd_2212531 1136091865972988195987261 := by
  unfold tailWord_2212531
  simp only [CollatzResearch.WordTrace]
  refine ⟨80697635147385532056125447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53798423431590354704083631 80697635147385532056125447)
  ·
    refine ⟨121046452721078298084188171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80697635147385532056125447 121046452721078298084188171)
    ·
      refine ⟨181569679081617447126282257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121046452721078298084188171 181569679081617447126282257)
      ·
        refine ⟨136177259311213085344711693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181569679081617447126282257 136177259311213085344711693)
        ·
          refine ⟨51066472241704907004266885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136177259311213085344711693 51066472241704907004266885)
          ·
            refine ⟨9574963545319670063300041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51066472241704907004266885 9574963545319670063300041)
            ·
              refine ⟨7181222658989752547475031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9574963545319670063300041 7181222658989752547475031)
              ·
                refine ⟨10771833988484628821212547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7181222658989752547475031 10771833988484628821212547)
                ·
                  refine ⟨16157750982726943231818821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10771833988484628821212547 16157750982726943231818821)
                  ·
                    refine ⟨3029578309261301855966029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16157750982726943231818821 3029578309261301855966029)
                    ·
                      refine ⟨1136091865972988195987261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3029578309261301855966029 1136091865972988195987261)
                      ·
                        rfl

theorem cell23_2212531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 4, 3].length) (baseStart_2212531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2212531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2212531 prefixEnd_2212531 := by exact prefixLift 2212531
  have htrace : WordTrace (prefixWord ++ tailWord_2212531) baseStart_2212531 baseEnd_2212531 := by
    simpa [prefixWord, tailWord_2212531, baseEnd_2212531] using wordTrace_append hprefix tailTrace_2212531
  have hstable : (prefixWord ++ tailWord_2212531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212531).length < 2 ^ (prefixWord ++ tailWord_2212531).sum := by decide
  have hdescent : baseEnd_2212531 < baseStart_2212531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212548 : List Nat := [2, 3, 3, 1, 1, 2, 1, 1, 4, 2, 3]
def baseStart_2212548 : Nat := 118140960795 + 2212548 * 2 ^ 59
def prefixEnd_2212548 : Nat := 4983230072969 + 3 ^ 40 * 2212548 * 2
def baseEnd_2212548 : Nat := 1136100595144114629474683

theorem tailTrace_2212548 : CollatzResearch.WordTrace tailWord_2212548 prefixEnd_2212548 1136100595144114629474683 := by
  unfold tailWord_2212548
  simp only [CollatzResearch.WordTrace]
  refine ⟨40349127594161971979747149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53798836792215962639662865 40349127594161971979747149)
  ·
    refine ⟨15130922847810739492405181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40349127594161971979747149 15130922847810739492405181)
    ·
      refine ⟨5674096067929027309651943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15130922847810739492405181 5674096067929027309651943)
      ·
        refine ⟨8511144101893540964477915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5674096067929027309651943 8511144101893540964477915)
        ·
          refine ⟨12766716152840311446716873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8511144101893540964477915 12766716152840311446716873)
          ·
            refine ⟨9575037114630233585037655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12766716152840311446716873 9575037114630233585037655)
            ·
              refine ⟨14362555671945350377556483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9575037114630233585037655 14362555671945350377556483)
              ·
                refine ⟨21543833507918025566334725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14362555671945350377556483 21543833507918025566334725)
                ·
                  refine ⟨4039468782734629793687761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21543833507918025566334725 4039468782734629793687761)
                  ·
                    refine ⟨3029601587050972345265821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4039468782734629793687761 3029601587050972345265821)
                    ·
                      refine ⟨1136100595144114629474683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3029601587050972345265821 1136100595144114629474683)
                      ·
                        rfl

theorem cell23_2212548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_2212548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2212548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2212548 prefixEnd_2212548 := by exact prefixLift 2212548
  have htrace : WordTrace (prefixWord ++ tailWord_2212548) baseStart_2212548 baseEnd_2212548 := by
    simpa [prefixWord, tailWord_2212548, baseEnd_2212548] using wordTrace_append hprefix tailTrace_2212548
  have hstable : (prefixWord ++ tailWord_2212548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212548).length < 2 ^ (prefixWord ++ tailWord_2212548).sum := by decide
  have hdescent : baseEnd_2212548 < baseStart_2212548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212568 : List Nat := [2, 1, 2, 2, 3, 2, 4, 1, 6]
def baseStart_2212568 : Nat := 118140960795 + 2212568 * 2 ^ 59
def prefixEnd_2212568 : Nat := 4983230072969 + 3 ^ 40 * 2212568 * 2
def baseEnd_2212568 : Nat := 126234540528578283469399

theorem tailTrace_2212568 : CollatzResearch.WordTrace tailWord_2212568 prefixEnd_2212568 126234540528578283469399 := by
  unfold tailWord_2212568
  simp only [CollatzResearch.WordTrace]
  refine ⟨40349492324125743687611179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53799323098834324916814905 40349492324125743687611179)
  ·
    refine ⟨60524238486188615531416769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40349492324125743687611179 60524238486188615531416769)
    ·
      refine ⟨45393178864641461648562577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60524238486188615531416769 45393178864641461648562577)
      ·
        refine ⟨34044884148481096236421933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45393178864641461648562577 34044884148481096236421933)
        ·
          refine ⟨12766831555680411088658225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34044884148481096236421933 12766831555680411088658225)
          ·
            refine ⟨9575123666760308316493669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12766831555680411088658225 9575123666760308316493669)
            ·
              refine ⟨1795335687517557809342563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9575123666760308316493669 1795335687517557809342563)
              ·
                refine ⟨2693003531276336714013845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1795335687517557809342563 2693003531276336714013845)
                ·
                  refine ⟨126234540528578283469399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2693003531276336714013845 126234540528578283469399)
                  ·
                    rfl

theorem cell23_2212568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 1, 6].length) (baseStart_2212568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2212568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2212568 prefixEnd_2212568 := by exact prefixLift 2212568
  have htrace : WordTrace (prefixWord ++ tailWord_2212568) baseStart_2212568 baseEnd_2212568 := by
    simpa [prefixWord, tailWord_2212568, baseEnd_2212568] using wordTrace_append hprefix tailTrace_2212568
  have hstable : (prefixWord ++ tailWord_2212568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212568).length < 2 ^ (prefixWord ++ tailWord_2212568).sum := by decide
  have hdescent : baseEnd_2212568 < baseStart_2212568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212595 : List Nat := [1, 1, 1, 2, 2, 3, 1, 7, 1, 1, 3]
def baseStart_2212595 : Nat := 118140960795 + 2212595 * 2 ^ 59
def prefixEnd_2212595 : Nat := 4983230072969 + 3 ^ 40 * 2212595 * 2
def baseEnd_2212595 : Nat := 1136124728734875945586967

theorem tailTrace_2212595 : CollatzResearch.WordTrace tailWord_2212595 prefixEnd_2212595 1136124728734875945586967 := by
  unfold tailWord_2212595
  simp only [CollatzResearch.WordTrace]
  refine ⟨80699969419153670986455239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53799979612769113990970159 80699969419153670986455239)
  ·
    refine ⟨121049954128730506479682859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80699969419153670986455239 121049954128730506479682859)
    ·
      refine ⟨181574931193095759719524289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121049954128730506479682859 181574931193095759719524289)
      ·
        refine ⟨136181198394821819789643217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181574931193095759719524289 136181198394821819789643217)
        ·
          refine ⟨102135898796116364842232413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136181198394821819789643217 102135898796116364842232413)
          ·
            refine ⟨38300962048543636815837155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102135898796116364842232413 38300962048543636815837155)
            ·
              refine ⟨57451443072815455223755733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38300962048543636815837155 57451443072815455223755733)
              ·
                refine ⟨1346518197019112231806775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 57451443072815455223755733 1346518197019112231806775)
                ·
                  refine ⟨2019777295528668347710163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1346518197019112231806775 2019777295528668347710163)
                  ·
                    refine ⟨3029665943293002521565245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2019777295528668347710163 3029665943293002521565245)
                    ·
                      refine ⟨1136124728734875945586967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3029665943293002521565245 1136124728734875945586967)
                      ·
                        rfl

theorem cell23_2212595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 7, 1, 1, 3].length) (baseStart_2212595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2212595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2212595 prefixEnd_2212595 := by exact prefixLift 2212595
  have htrace : WordTrace (prefixWord ++ tailWord_2212595) baseStart_2212595 baseEnd_2212595 := by
    simpa [prefixWord, tailWord_2212595, baseEnd_2212595] using wordTrace_append hprefix tailTrace_2212595
  have hstable : (prefixWord ++ tailWord_2212595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212595).length < 2 ^ (prefixWord ++ tailWord_2212595).sum := by decide
  have hdescent : baseEnd_2212595 < baseStart_2212595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212612 : List Nat := [2, 3, 2, 2, 1, 1, 3, 4, 1, 1, 3]
def baseStart_2212612 : Nat := 118140960795 + 2212612 * 2 ^ 59
def prefixEnd_2212612 : Nat := 4983230072969 + 3 ^ 40 * 2212612 * 2
def baseEnd_2212612 : Nat := 1136133457906002379074389

theorem tailTrace_2212612 : CollatzResearch.WordTrace tailWord_2212612 prefixEnd_2212612 1136133457906002379074389 := by
  unfold tailWord_2212612
  simp only [CollatzResearch.WordTrace]
  refine ⟨40350294730046041444912045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53800392973394721926549393 40350294730046041444912045)
  ·
    refine ⟨15131360523767265541842017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40350294730046041444912045 15131360523767265541842017)
    ·
      refine ⟨11348520392825449156381513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15131360523767265541842017 11348520392825449156381513)
      ·
        refine ⟨8511390294619086867286135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11348520392825449156381513 8511390294619086867286135)
        ·
          refine ⟨12767085441928630300929203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8511390294619086867286135 12767085441928630300929203)
          ·
            refine ⟨19150628162892945451393805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12767085441928630300929203 19150628162892945451393805)
            ·
              refine ⟨7181485561084854544272677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19150628162892945451393805 7181485561084854544272677)
              ·
                refine ⟨1346528542703410227051127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7181485561084854544272677 1346528542703410227051127)
                ·
                  refine ⟨2019792814055115340576691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1346528542703410227051127 2019792814055115340576691)
                  ·
                    refine ⟨3029689221082673010865037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2019792814055115340576691 3029689221082673010865037)
                    ·
                      refine ⟨1136133457906002379074389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3029689221082673010865037 1136133457906002379074389)
                      ·
                        rfl

theorem cell23_2212612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_2212612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2212612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2212612 prefixEnd_2212612 := by exact prefixLift 2212612
  have htrace : WordTrace (prefixWord ++ tailWord_2212612) baseStart_2212612 baseEnd_2212612 := by
    simpa [prefixWord, tailWord_2212612, baseEnd_2212612] using wordTrace_append hprefix tailTrace_2212612
  have hstable : (prefixWord ++ tailWord_2212612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212612).length < 2 ^ (prefixWord ++ tailWord_2212612).sum := by decide
  have hdescent : baseEnd_2212612 < baseStart_2212612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212648 : List Nat := [2, 1, 5, 1, 1, 1, 1, 4, 1, 2, 4]
def baseStart_2212648 : Nat := 118140960795 + 2212648 * 2 ^ 59
def prefixEnd_2212648 : Nat := 4983230072969 + 3 ^ 40 * 2212648 * 2
def baseEnd_2212648 : Nat := 1136151943209564238224223

theorem tailTrace_2212648 : CollatzResearch.WordTrace tailWord_2212648 prefixEnd_2212648 1136151943209564238224223 := by
  unfold tailWord_2212648
  simp only [CollatzResearch.WordTrace]
  refine ⟨40350951243980830519067299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53801268325307774025423065 40350951243980830519067299)
  ·
    refine ⟨60526426865971245778600949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40350951243980830519067299 60526426865971245778600949)
    ·
      refine ⟨5674352518684804291743839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60526426865971245778600949 5674352518684804291743839)
      ·
        refine ⟨8511528778027206437615759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5674352518684804291743839 8511528778027206437615759)
        ·
          refine ⟨12767293167040809656423639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8511528778027206437615759 12767293167040809656423639)
          ·
            refine ⟨19150939750561214484635459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12767293167040809656423639 19150939750561214484635459)
            ·
              refine ⟨28726409625841821726953189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19150939750561214484635459 28726409625841821726953189)
              ·
                refine ⟨5386201804845341573803723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28726409625841821726953189 5386201804845341573803723)
                ·
                  refine ⟨8079302707268012360705585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5386201804845341573803723 8079302707268012360705585)
                  ·
                    refine ⟨6059477030451009270529189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8079302707268012360705585 6059477030451009270529189)
                    ·
                      refine ⟨1136151943209564238224223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6059477030451009270529189 1136151943209564238224223)
                      ·
                        rfl

theorem cell23_2212648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_2212648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2212648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2212648 prefixEnd_2212648 := by exact prefixLift 2212648
  have htrace : WordTrace (prefixWord ++ tailWord_2212648) baseStart_2212648 baseEnd_2212648 := by
    simpa [prefixWord, tailWord_2212648, baseEnd_2212648] using wordTrace_append hprefix tailTrace_2212648
  have hstable : (prefixWord ++ tailWord_2212648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212648).length < 2 ^ (prefixWord ++ tailWord_2212648).sum := by decide
  have hdescent : baseEnd_2212648 < baseStart_2212648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212662 : List Nat := [5, 1, 2, 2, 2, 1, 1, 1, 4, 4]
def baseStart_2212662 : Nat := 118140960795 + 2212662 * 2 ^ 59
def prefixEnd_2212662 : Nat := 4983230072969 + 3 ^ 40 * 2212662 * 2
def baseEnd_2212662 : Nat := 378719710646242394483053

theorem tailTrace_2212662 : CollatzResearch.WordTrace tailWord_2212662 prefixEnd_2212662 378719710646242394483053 := by
  unfold tailWord_2212662
  simp only [CollatzResearch.WordTrace]
  refine ⟨5043900819369433839321515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53801608739940627619429493 5043900819369433839321515)
  ·
    refine ⟨7565851229054150758982273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5043900819369433839321515 7565851229054150758982273)
    ·
      refine ⟨5674388421790613069236705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7565851229054150758982273 5674388421790613069236705)
      ·
        refine ⟨4255791316342959801927529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5674388421790613069236705 4255791316342959801927529)
        ·
          refine ⟨3191843487257219851445647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4255791316342959801927529 3191843487257219851445647)
          ·
            refine ⟨4787765230885829777168471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3191843487257219851445647 4787765230885829777168471)
            ·
              refine ⟨7181647846328744665752707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4787765230885829777168471 7181647846328744665752707)
              ·
                refine ⟨10772471769493116998629061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7181647846328744665752707 10772471769493116998629061)
                ·
                  refine ⟨2019838456779959437242949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10772471769493116998629061 2019838456779959437242949)
                  ·
                    refine ⟨378719710646242394483053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2019838456779959437242949 378719710646242394483053)
                    ·
                      rfl

theorem cell23_2212662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_2212662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2212662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2212662 prefixEnd_2212662 := by exact prefixLift 2212662
  have htrace : WordTrace (prefixWord ++ tailWord_2212662) baseStart_2212662 baseEnd_2212662 := by
    simpa [prefixWord, tailWord_2212662, baseEnd_2212662] using wordTrace_append hprefix tailTrace_2212662
  have hstable : (prefixWord ++ tailWord_2212662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212662).length < 2 ^ (prefixWord ++ tailWord_2212662).sum := by decide
  have hdescent : baseEnd_2212662 < baseStart_2212662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212669 : List Nat := [1, 4, 1, 4, 2, 1, 2, 1, 3, 2, 2]
def baseStart_2212669 : Nat := 118140960795 + 2212669 * 2 ^ 59
def prefixEnd_2212669 : Nat := 4983230072969 + 3 ^ 40 * 2212669 * 2
def baseEnd_2212669 : Nat := 1136162726303308656061627

theorem tailTrace_2212669 : CollatzResearch.WordTrace tailWord_2212669 prefixEnd_2212669 1136162726303308656061627 := by
  unfold tailWord_2212669
  simp only [CollatzResearch.WordTrace]
  refine ⟨80702668420885581624649061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53801778947257054416432707 80702668420885581624649061)
  ·
    refine ⟨15131750328916046554621699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80702668420885581624649061 15131750328916046554621699)
    ·
      refine ⟨22697625493374069831932549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15131750328916046554621699 22697625493374069831932549)
      ·
        refine ⟨4255804780007638093487353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22697625493374069831932549 4255804780007638093487353)
        ·
          refine ⟨3191853585005728570115515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4255804780007638093487353 3191853585005728570115515)
          ·
            refine ⟨4787780377508592855173273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3191853585005728570115515 4787780377508592855173273)
            ·
              refine ⟨3590835283131444641379955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4787780377508592855173273 3590835283131444641379955)
              ·
                refine ⟨5386252924697166962069933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3590835283131444641379955 5386252924697166962069933)
                ·
                  refine ⟨2019844846761437610776225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5386252924697166962069933 2019844846761437610776225)
                  ·
                    refine ⟨1514883635071078208082169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2019844846761437610776225 1514883635071078208082169)
                    ·
                      refine ⟨1136162726303308656061627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1514883635071078208082169 1136162726303308656061627)
                      ·
                        rfl

theorem cell23_2212669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_2212669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2212669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2212669 prefixEnd_2212669 := by exact prefixLift 2212669
  have htrace : WordTrace (prefixWord ++ tailWord_2212669) baseStart_2212669 baseEnd_2212669 := by
    simpa [prefixWord, tailWord_2212669, baseEnd_2212669] using wordTrace_append hprefix tailTrace_2212669
  have hstable : (prefixWord ++ tailWord_2212669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212669).length < 2 ^ (prefixWord ++ tailWord_2212669).sum := by decide
  have hdescent : baseEnd_2212669 < baseStart_2212669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212691 : List Nat := [1, 1, 1, 2, 1, 1, 3, 4, 2, 3, 4]
def baseStart_2212691 : Nat := 118140960795 + 2212691 * 2 ^ 59
def prefixEnd_2212691 : Nat := 4983230072969 + 3 ^ 40 * 2212691 * 2
def baseEnd_2212691 : Nat := 1136174022877707569986525

theorem tailTrace_2212691 : CollatzResearch.WordTrace tailWord_2212691 prefixEnd_2212691 1136174022877707569986525 := by
  unfold tailWord_2212691
  simp only [CollatzResearch.WordTrace]
  refine ⟨80703470826805879381949927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53802313884537252921299951 80703470826805879381949927)
  ·
    refine ⟨121055206240208819072924891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80703470826805879381949927 121055206240208819072924891)
    ·
      refine ⟨181582809360313228609387337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121055206240208819072924891 181582809360313228609387337)
      ·
        refine ⟨136187107020234921457040503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181582809360313228609387337 136187107020234921457040503)
        ·
          refine ⟨204280660530352382185560755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136187107020234921457040503 204280660530352382185560755)
          ·
            refine ⟨306420990795528573278341133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204280660530352382185560755 306420990795528573278341133)
            ·
              refine ⟨114907871548323214979377925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 306420990795528573278341133 114907871548323214979377925)
              ·
                refine ⟨21545225915310602808633361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 114907871548323214979377925 21545225915310602808633361)
                ·
                  refine ⟨16158919436482952106475021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21545225915310602808633361 16158919436482952106475021)
                  ·
                    refine ⟨6059594788681107039928133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16158919436482952106475021 6059594788681107039928133)
                    ·
                      refine ⟨1136174022877707569986525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6059594788681107039928133 1136174022877707569986525)
                      ·
                        rfl

theorem cell23_2212691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 3, 4].length) (baseStart_2212691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2212691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2212691 prefixEnd_2212691 := by exact prefixLift 2212691
  have htrace : WordTrace (prefixWord ++ tailWord_2212691) baseStart_2212691 baseEnd_2212691 := by
    simpa [prefixWord, tailWord_2212691, baseEnd_2212691] using wordTrace_append hprefix tailTrace_2212691
  have hstable : (prefixWord ++ tailWord_2212691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212691).length < 2 ^ (prefixWord ++ tailWord_2212691).sum := by decide
  have hdescent : baseEnd_2212691 < baseStart_2212691 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212692 : List Nat := [2, 4, 1, 1, 5, 1, 2, 7]
def baseStart_2212692 : Nat := 118140960795 + 2212692 * 2 ^ 59
def prefixEnd_2212692 : Nat := 4983230072969 + 3 ^ 40 * 2212692 * 2
def baseEnd_2212692 : Nat := 42080538383643039484223

theorem tailTrace_2212692 : CollatzResearch.WordTrace tailWord_2212692 prefixEnd_2212692 42080538383643039484223 := by
  unfold tailWord_2212692
  simp only [CollatzResearch.WordTrace]
  refine ⟨40351753649901128276368165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53802338199868171035157553 40351753649901128276368165)
  ·
    refine ⟨7565953809356461551819031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40351753649901128276368165 7565953809356461551819031)
    ·
      refine ⟨11348930714034692327728547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7565953809356461551819031 11348930714034692327728547)
      ·
        refine ⟨17023396071052038491592821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11348930714034692327728547 17023396071052038491592821)
        ·
          refine ⟨1595943381661128608586827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17023396071052038491592821 1595943381661128608586827)
          ·
            refine ⟨2393915072491692912880241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1595943381661128608586827 2393915072491692912880241)
            ·
              refine ⟨1795436304368769684660181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2393915072491692912880241 1795436304368769684660181)
              ·
                refine ⟨42080538383643039484223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1795436304368769684660181 42080538383643039484223)
                ·
                  rfl

theorem cell23_2212692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 7].length) (baseStart_2212692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2212692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2212692 prefixEnd_2212692 := by exact prefixLift 2212692
  have htrace : WordTrace (prefixWord ++ tailWord_2212692) baseStart_2212692 baseEnd_2212692 := by
    simpa [prefixWord, tailWord_2212692, baseEnd_2212692] using wordTrace_append hprefix tailTrace_2212692
  have hstable : (prefixWord ++ tailWord_2212692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212692).length < 2 ^ (prefixWord ++ tailWord_2212692).sum := by decide
  have hdescent : baseEnd_2212692 < baseStart_2212692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212712 : List Nat := [2, 1, 4, 2, 1, 2, 2, 3, 1, 3, 2]
def baseStart_2212712 : Nat := 118140960795 + 2212712 * 2 ^ 59
def prefixEnd_2212712 : Nat := 4983230072969 + 3 ^ 40 * 2212712 * 2
def baseEnd_2212712 : Nat := 1136184805971451987823929

theorem tailTrace_2212712 : CollatzResearch.WordTrace tailWord_2212712 prefixEnd_2212712 1136184805971451987823929 := by
  unfold tailWord_2212712
  simp only [CollatzResearch.WordTrace]
  refine ⟨40352118379864899984232195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53802824506486533312309593 40352118379864899984232195)
  ·
    refine ⟨60528177569797349976348293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40352118379864899984232195 60528177569797349976348293)
    ·
      refine ⟨11349033294337003120565305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60528177569797349976348293 11349033294337003120565305)
      ·
        refine ⟨8511774970752752340423979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11349033294337003120565305 8511774970752752340423979)
        ·
          refine ⟨12767662456129128510635969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8511774970752752340423979 12767662456129128510635969)
          ·
            refine ⟨9575746842096846382976977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12767662456129128510635969 9575746842096846382976977)
            ·
              refine ⟨7181810131572634787232733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9575746842096846382976977 7181810131572634787232733)
              ·
                refine ⟨2693178799339738045212275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7181810131572634787232733 2693178799339738045212275)
                ·
                  refine ⟨4039768199009607067818413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2693178799339738045212275 4039768199009607067818413)
                  ·
                    refine ⟨1514913074628602650431905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4039768199009607067818413 1514913074628602650431905)
                    ·
                      refine ⟨1136184805971451987823929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1514913074628602650431905 1136184805971451987823929)
                      ·
                        rfl

theorem cell23_2212712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_2212712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2212712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2212712 prefixEnd_2212712 := by exact prefixLift 2212712
  have htrace : WordTrace (prefixWord ++ tailWord_2212712) baseStart_2212712 baseEnd_2212712 := by
    simpa [prefixWord, tailWord_2212712, baseEnd_2212712] using wordTrace_append hprefix tailTrace_2212712
  have hstable : (prefixWord ++ tailWord_2212712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212712).length < 2 ^ (prefixWord ++ tailWord_2212712).sum := by decide
  have hdescent : baseEnd_2212712 < baseStart_2212712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212765 : List Nat := [1, 4, 2, 1, 2, 1, 2, 5, 5]
def baseStart_2212765 : Nat := 118140960795 + 2212765 * 2 ^ 59
def prefixEnd_2212765 : Nat := 4983230072969 + 3 ^ 40 * 2212765 * 2
def baseEnd_2212765 : Nat := 126245780049571142273465

theorem tailTrace_2212765 : CollatzResearch.WordTrace tailWord_2212765 prefixEnd_2212765 126245780049571142273465 := by
  unfold tailWord_2212765
  simp only [CollatzResearch.WordTrace]
  refine ⟨80706169828537790020143749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53804113219025193346762499 80706169828537790020143749)
  ·
    refine ⟨15132406842850835628776953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80706169828537790020143749 15132406842850835628776953)
    ·
      refine ⟨11349305132138126721582715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15132406842850835628776953 11349305132138126721582715)
      ·
        refine ⟨17023957698207190082374073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11349305132138126721582715 17023957698207190082374073)
        ·
          refine ⟨12767968273655392561780555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17023957698207190082374073 12767968273655392561780555)
          ·
            refine ⟨19151952410483088842670833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12767968273655392561780555 19151952410483088842670833)
            ·
              refine ⟨14363964307862316632003125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19151952410483088842670833 14363964307862316632003125)
              ·
                refine ⟨1346621653862092184250293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14363964307862316632003125 1346621653862092184250293)
                ·
                  refine ⟨126245780049571142273465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1346621653862092184250293 126245780049571142273465)
                  ·
                    rfl

theorem cell23_2212765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 5, 5].length) (baseStart_2212765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2212765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2212765 prefixEnd_2212765 := by exact prefixLift 2212765
  have htrace : WordTrace (prefixWord ++ tailWord_2212765) baseStart_2212765 baseEnd_2212765 := by
    simpa [prefixWord, tailWord_2212765, baseEnd_2212765] using wordTrace_append hprefix tailTrace_2212765
  have hstable : (prefixWord ++ tailWord_2212765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212765).length < 2 ^ (prefixWord ++ tailWord_2212765).sum := by decide
  have hdescent : baseEnd_2212765 < baseStart_2212765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212815 : List Nat := [1, 1, 2, 1, 1, 6, 3, 1, 2, 1, 4]
def baseStart_2212815 : Nat := 118140960795 + 2212815 * 2 ^ 59
def prefixEnd_2212815 : Nat := 4983230072969 + 3 ^ 40 * 2212815 * 2
def baseEnd_2212815 : Nat := 1136237694478865084835955

theorem tailTrace_2212815 : CollatzResearch.WordTrace tailWord_2212815 prefixEnd_2212815 1136237694478865084835955 := by
  unfold tailWord_2212815
  simp only [CollatzResearch.WordTrace]
  refine ⟨80707993478356648559463899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53805328985571099039642599 80707993478356648559463899)
  ·
    refine ⟨121061990217534972839195849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80707993478356648559463899 121061990217534972839195849)
    ·
      refine ⟨90796492663151229629396887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121061990217534972839195849 90796492663151229629396887)
      ·
        refine ⟨136194738994726844444095331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90796492663151229629396887 136194738994726844444095331)
        ·
          refine ⟨204292108492090266666142997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136194738994726844444095331 204292108492090266666142997)
          ·
            refine ⟨9576192585566731249975453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 204292108492090266666142997 9576192585566731249975453)
            ·
              refine ⟨3591072219587524218740795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9576192585566731249975453 3591072219587524218740795)
              ·
                refine ⟨5386608329381286328111193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3591072219587524218740795 5386608329381286328111193)
                ·
                  refine ⟨4039956247035964746083395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5386608329381286328111193 4039956247035964746083395)
                  ·
                    refine ⟨6059934370553947119125093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4039956247035964746083395 6059934370553947119125093)
                    ·
                      refine ⟨1136237694478865084835955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6059934370553947119125093 1136237694478865084835955)
                      ·
                        rfl

theorem cell23_2212815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 2, 1, 4].length) (baseStart_2212815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2212815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2212815 prefixEnd_2212815 := by exact prefixLift 2212815
  have htrace : WordTrace (prefixWord ++ tailWord_2212815) baseStart_2212815 baseEnd_2212815 := by
    simpa [prefixWord, tailWord_2212815, baseEnd_2212815] using wordTrace_append hprefix tailTrace_2212815
  have hstable : (prefixWord ++ tailWord_2212815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212815).length < 2 ^ (prefixWord ++ tailWord_2212815).sum := by decide
  have hdescent : baseEnd_2212815 < baseStart_2212815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212835 : List Nat := [1, 1, 1, 6, 1, 1, 2, 1, 4, 2, 3]
def baseStart_2212835 : Nat := 118140960795 + 2212835 * 2 ^ 59
def prefixEnd_2212835 : Nat := 4983230072969 + 3 ^ 40 * 2212835 * 2
def baseEnd_2212835 : Nat := 1136247964091955006585863

theorem tailTrace_2212835 : CollatzResearch.WordTrace tailWord_2212835 prefixEnd_2212835 1136247964091955006585863 := by
  unfold tailWord_2212835
  simp only [CollatzResearch.WordTrace]
  refine ⟨80708722938284191975191959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53805815292189461316794639 80708722938284191975191959)
  ·
    refine ⟨121063084407426287962787939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80708722938284191975191959 121063084407426287962787939)
    ·
      refine ⟨181594626611139431944181909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121063084407426287962787939 181594626611139431944181909)
      ·
        refine ⟨8512248122397160872383527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 181594626611139431944181909 8512248122397160872383527)
        ·
          refine ⟨12768372183595741308575291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8512248122397160872383527 12768372183595741308575291)
          ·
            refine ⟨19152558275393611962862937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12768372183595741308575291 19152558275393611962862937)
            ·
              refine ⟨14364418706545208972147203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19152558275393611962862937 14364418706545208972147203)
              ·
                refine ⟨21546628059817813458220805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14364418706545208972147203 21546628059817813458220805)
                ·
                  refine ⟨4039992761215840023416401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21546628059817813458220805 4039992761215840023416401)
                  ·
                    refine ⟨3029994570911880017562301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4039992761215840023416401 3029994570911880017562301)
                    ·
                      refine ⟨1136247964091955006585863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3029994570911880017562301 1136247964091955006585863)
                      ·
                        rfl

theorem cell23_2212835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_2212835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2212835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2212835 prefixEnd_2212835 := by exact prefixLift 2212835
  have htrace : WordTrace (prefixWord ++ tailWord_2212835) baseStart_2212835 baseEnd_2212835 := by
    simpa [prefixWord, tailWord_2212835, baseEnd_2212835] using wordTrace_append hprefix tailTrace_2212835
  have hstable : (prefixWord ++ tailWord_2212835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212835).length < 2 ^ (prefixWord ++ tailWord_2212835).sum := by decide
  have hdescent : baseEnd_2212835 < baseStart_2212835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212842 : List Nat := [3, 1, 3, 1, 2, 3, 2, 1, 3, 4]
def baseStart_2212842 : Nat := 118140960795 + 2212842 * 2 ^ 59
def prefixEnd_2212842 : Nat := 4983230072969 + 3 ^ 40 * 2212842 * 2
def baseEnd_2212842 : Nat := 378750519485512159732777

theorem tailTrace_2212842 : CollatzResearch.WordTrace tailWord_2212842 prefixEnd_2212842 378750519485512159732777 := by
  unfold tailWord_2212842
  simp only [CollatzResearch.WordTrace]
  refine ⟨20177244562314708042674195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53805985499505888113797853 20177244562314708042674195)
  ·
    refine ⟨30265866843472062064011293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20177244562314708042674195 30265866843472062064011293)
    ·
      refine ⟨11349700066302023274004235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30265866843472062064011293 11349700066302023274004235)
      ·
        refine ⟨17024550099453034911006353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11349700066302023274004235 17024550099453034911006353)
        ·
          refine ⟨12768412574589776183254765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17024550099453034911006353 12768412574589776183254765)
          ·
            refine ⟨4788154715471166068720537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12768412574589776183254765 4788154715471166068720537)
            ·
              refine ⟨3591116036603374551540403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4788154715471166068720537 3591116036603374551540403)
              ·
                refine ⟨5386674054905061827310605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3591116036603374551540403 5386674054905061827310605)
                ·
                  refine ⟨2020002770589398185241477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5386674054905061827310605 2020002770589398185241477)
                  ·
                    refine ⟨378750519485512159732777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2020002770589398185241477 378750519485512159732777)
                    ·
                      rfl

theorem cell23_2212842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_2212842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2212842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2212842 prefixEnd_2212842 := by exact prefixLift 2212842
  have htrace : WordTrace (prefixWord ++ tailWord_2212842) baseStart_2212842 baseEnd_2212842 := by
    simpa [prefixWord, tailWord_2212842, baseEnd_2212842] using wordTrace_append hprefix tailTrace_2212842
  have hstable : (prefixWord ++ tailWord_2212842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212842).length < 2 ^ (prefixWord ++ tailWord_2212842).sum := by decide
  have hdescent : baseEnd_2212842 < baseStart_2212842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212899 : List Nat := [1, 1, 1, 4, 3, 4, 1, 1, 3, 1, 3]
def baseStart_2212899 : Nat := 118140960795 + 2212899 * 2 ^ 59
def prefixEnd_2212899 : Nat := 4983230072969 + 3 ^ 40 * 2212899 * 2
def baseEnd_2212899 : Nat := 1136280826853842756185569

theorem tailTrace_2212899 : CollatzResearch.WordTrace tailWord_2212899 prefixEnd_2212899 1136280826853842756185569 := by
  unfold tailWord_2212899
  simp only [CollatzResearch.WordTrace]
  refine ⟨80711057210052330905521751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53807371473368220603681167 80711057210052330905521751)
  ·
    refine ⟨121066585815078496358282627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80711057210052330905521751 121066585815078496358282627)
    ·
      refine ⟨181599878722617744537423941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121066585815078496358282627 181599878722617744537423941)
      ·
        refine ⟨34049977260490827100766989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 181599878722617744537423941 34049977260490827100766989)
        ·
          refine ⟨12768741472684060162787621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34049977260490827100766989 12768741472684060162787621)
          ·
            refine ⟨2394139026128261280522679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12768741472684060162787621 2394139026128261280522679)
            ·
              refine ⟨3591208539192391920784019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2394139026128261280522679 3591208539192391920784019)
              ·
                refine ⟨5386812808788587881176029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3591208539192391920784019 5386812808788587881176029)
                ·
                  refine ⟨2020054803295720455441011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5386812808788587881176029 2020054803295720455441011)
                  ·
                    refine ⟨3030082204943580683161517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2020054803295720455441011 3030082204943580683161517)
                    ·
                      refine ⟨1136280826853842756185569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3030082204943580683161517 1136280826853842756185569)
                      ·
                        rfl

theorem cell23_2212899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 3, 1, 3].length) (baseStart_2212899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2212899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2212899 prefixEnd_2212899 := by exact prefixLift 2212899
  have htrace : WordTrace (prefixWord ++ tailWord_2212899) baseStart_2212899 baseEnd_2212899 := by
    simpa [prefixWord, tailWord_2212899, baseEnd_2212899] using wordTrace_append hprefix tailTrace_2212899
  have hstable : (prefixWord ++ tailWord_2212899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212899).length < 2 ^ (prefixWord ++ tailWord_2212899).sum := by decide
  have hdescent : baseEnd_2212899 < baseStart_2212899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212906 : List Nat := [3, 1, 4, 1, 4, 1, 2, 1, 6]
def baseStart_2212906 : Nat := 118140960795 + 2212906 * 2 ^ 59
def prefixEnd_2212906 : Nat := 4983230072969 + 3 ^ 40 * 2212906 * 2
def baseEnd_2212906 : Nat := 126253824579824914310893

theorem tailTrace_2212906 : CollatzResearch.WordTrace tailWord_2212906 prefixEnd_2212906 126253824579824914310893 := by
  unfold tailWord_2212906
  simp only [CollatzResearch.WordTrace]
  refine ⟨20177828130256742775256643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53807541680684647400684381 20177828130256742775256643)
  ·
    refine ⟨30266742195385114162884965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20177828130256742775256643 30266742195385114162884965)
    ·
      refine ⟨5675014161634708905540931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30266742195385114162884965 5675014161634708905540931)
      ·
        refine ⟨8512521242452063358311397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5675014161634708905540931 8512521242452063358311397)
        ·
          refine ⟨1596097732959761879683387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8512521242452063358311397 1596097732959761879683387)
          ·
            refine ⟨2394146599439642819525081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1596097732959761879683387 2394146599439642819525081)
            ·
              refine ⟨1795609949579732114643811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2394146599439642819525081 1795609949579732114643811)
              ·
                refine ⟨2693414924369598171965717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1795609949579732114643811 2693414924369598171965717)
                ·
                  refine ⟨126253824579824914310893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2693414924369598171965717 126253824579824914310893)
                  ·
                    rfl

theorem cell23_2212906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 1, 6].length) (baseStart_2212906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2212906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2212906 prefixEnd_2212906 := by exact prefixLift 2212906
  have htrace : WordTrace (prefixWord ++ tailWord_2212906) baseStart_2212906 baseEnd_2212906 := by
    simpa [prefixWord, tailWord_2212906, baseEnd_2212906] using wordTrace_append hprefix tailTrace_2212906
  have hstable : (prefixWord ++ tailWord_2212906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212906).length < 2 ^ (prefixWord ++ tailWord_2212906).sum := by decide
  have hdescent : baseEnd_2212906 < baseStart_2212906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212922 : List Nat := [3, 1, 1, 1, 3, 1, 5, 2, 1, 1, 4]
def baseStart_2212922 : Nat := 118140960795 + 2212922 * 2 ^ 59
def prefixEnd_2212922 : Nat := 4983230072969 + 3 ^ 40 * 2212922 * 2
def baseEnd_2212922 : Nat := 1136292636908896166197963

theorem tailTrace_2212922 : CollatzResearch.WordTrace tailWord_2212922 prefixEnd_2212922 1136292636908896166197963 := by
  unfold tailWord_2212922
  simp only [CollatzResearch.WordTrace]
  refine ⟨20177974022242251458402255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53807930725979337222406013 20177974022242251458402255)
  ·
    refine ⟨30266961033363377187603383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20177974022242251458402255 30266961033363377187603383)
    ·
      refine ⟨45400441550045065781405075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30266961033363377187603383 45400441550045065781405075)
      ·
        refine ⟨68100662325067598672107613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45400441550045065781405075 68100662325067598672107613)
        ·
          refine ⟨25537748371900349502040355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68100662325067598672107613 25537748371900349502040355)
          ·
            refine ⟨38306622557850524253060533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25537748371900349502040355 38306622557850524253060533)
            ·
              refine ⟨3591245864798486648724425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38306622557850524253060533 3591245864798486648724425)
              ·
                refine ⟨2693434398598864986543319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3591245864798486648724425 2693434398598864986543319)
                ·
                  refine ⟨4040151597898297479814979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2693434398598864986543319 4040151597898297479814979)
                  ·
                    refine ⟨6060227396847446219722469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4040151597898297479814979 6060227396847446219722469)
                    ·
                      refine ⟨1136292636908896166197963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6060227396847446219722469 1136292636908896166197963)
                      ·
                        rfl

theorem cell23_2212922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 2, 1, 1, 4].length) (baseStart_2212922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2212922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2212922 prefixEnd_2212922 := by exact prefixLift 2212922
  have htrace : WordTrace (prefixWord ++ tailWord_2212922) baseStart_2212922 baseEnd_2212922 := by
    simpa [prefixWord, tailWord_2212922, baseEnd_2212922] using wordTrace_append hprefix tailTrace_2212922
  have hstable : (prefixWord ++ tailWord_2212922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212922).length < 2 ^ (prefixWord ++ tailWord_2212922).sum := by decide
  have hdescent : baseEnd_2212922 < baseStart_2212922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212926 : List Nat := [4, 2, 1, 3, 1, 2, 2, 1, 2, 3, 2]
def baseStart_2212926 : Nat := 118140960795 + 2212926 * 2 ^ 59
def prefixEnd_2212926 : Nat := 4983230072969 + 3 ^ 40 * 2212926 * 2
def baseEnd_2212926 : Nat := 1136294690831514150547945

theorem tailTrace_2212926 : CollatzResearch.WordTrace tailWord_2212926 prefixEnd_2212926 1136294690831514150547945 := by
  unfold tailWord_2212926
  simp only [CollatzResearch.WordTrace]
  refine ⟨10089005247619314314594329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53808027987303009677836421 10089005247619314314594329)
  ·
    refine ⟨7566753935714485735945747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10089005247619314314594329 7566753935714485735945747)
    ·
      refine ⟨11350130903571728603918621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7566753935714485735945747 11350130903571728603918621)
      ·
        refine ⟨4256299088839398226469483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11350130903571728603918621 4256299088839398226469483)
        ·
          refine ⟨6384448633259097339704225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4256299088839398226469483 6384448633259097339704225)
          ·
            refine ⟨4788336474944323004778169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6384448633259097339704225 4788336474944323004778169)
            ·
              refine ⟨3591252356208242253583627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4788336474944323004778169 3591252356208242253583627)
              ·
                refine ⟨5386878534312363380375441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3591252356208242253583627 5386878534312363380375441)
                ·
                  refine ⟨4040158900734272535281581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5386878534312363380375441 4040158900734272535281581)
                  ·
                    refine ⟨1515059587775352200730593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4040158900734272535281581 1515059587775352200730593)
                    ·
                      refine ⟨1136294690831514150547945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1515059587775352200730593 1136294690831514150547945)
                      ·
                        rfl

theorem cell23_2212926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_2212926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2212926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2212926 prefixEnd_2212926 := by exact prefixLift 2212926
  have htrace : WordTrace (prefixWord ++ tailWord_2212926) baseStart_2212926 baseEnd_2212926 := by
    simpa [prefixWord, tailWord_2212926, baseEnd_2212926] using wordTrace_append hprefix tailTrace_2212926
  have hstable : (prefixWord ++ tailWord_2212926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212926).length < 2 ^ (prefixWord ++ tailWord_2212926).sum := by decide
  have hdescent : baseEnd_2212926 < baseStart_2212926 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212928 : List Nat := [2, 1, 1, 2, 2, 3, 1, 11]
def baseStart_2212928 : Nat := 118140960795 + 2212928 * 2 ^ 59
def prefixEnd_2212928 : Nat := 4983230072969 + 3 ^ 40 * 2212928 * 2
def baseEnd_2212928 : Nat := 42085026584919375656405

theorem tailTrace_2212928 : CollatzResearch.WordTrace tailWord_2212928 prefixEnd_2212928 42085026584919375656405 := by
  unfold tailWord_2212928
  simp only [CollatzResearch.WordTrace]
  refine ⟨40356057463473634429163719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53808076617964845905551625 40356057463473634429163719)
  ·
    refine ⟨60534086195210451643745579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40356057463473634429163719 60534086195210451643745579)
    ·
      refine ⟨90801129292815677465618369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60534086195210451643745579 90801129292815677465618369)
      ·
        refine ⟨68100846969611758099213777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90801129292815677465618369 68100846969611758099213777)
        ·
          refine ⟨51075635227208818574410333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68100846969611758099213777 51075635227208818574410333)
          ·
            refine ⟨19153363210203306965403875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51075635227208818574410333 19153363210203306965403875)
            ·
              refine ⟨28730044815304960448105813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19153363210203306965403875 28730044815304960448105813)
              ·
                refine ⟨42085026584919375656405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 28730044815304960448105813 42085026584919375656405)
                ·
                  rfl

theorem cell23_2212928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 11].length) (baseStart_2212928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2212928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2212928 prefixEnd_2212928 := by exact prefixLift 2212928
  have htrace : WordTrace (prefixWord ++ tailWord_2212928) baseStart_2212928 baseEnd_2212928 := by
    simpa [prefixWord, tailWord_2212928, baseEnd_2212928] using wordTrace_append hprefix tailTrace_2212928
  have hstable : (prefixWord ++ tailWord_2212928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212928).length < 2 ^ (prefixWord ++ tailWord_2212928).sum := by decide
  have hdescent : baseEnd_2212928 < baseStart_2212928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212935 : List Nat := [1, 1, 4, 1, 3, 2, 1, 1, 3, 2, 4]
def baseStart_2212935 : Nat := 118140960795 + 2212935 * 2 ^ 59
def prefixEnd_2212935 : Nat := 4983230072969 + 3 ^ 40 * 2212935 * 2
def baseEnd_2212935 : Nat := 1136299312157404615335403

theorem tailTrace_2212935 : CollatzResearch.WordTrace tailWord_2212935 prefixEnd_2212935 1136299312157404615335403 := by
  unfold tailWord_2212935
  simp only [CollatzResearch.WordTrace]
  refine ⟨80712370237921909053832259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53808246825281272702554839 80712370237921909053832259)
  ·
    refine ⟨121068555356882863580748389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80712370237921909053832259 121068555356882863580748389)
    ·
      refine ⟨22700354129415536921390323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121068555356882863580748389 22700354129415536921390323)
      ·
        refine ⟨34050531194123305382085485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22700354129415536921390323 34050531194123305382085485)
        ·
          refine ⟨12768949197796239518282057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34050531194123305382085485 12768949197796239518282057)
          ·
            refine ⟨9576711898347179638711543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12768949197796239518282057 9576711898347179638711543)
            ·
              refine ⟨14365067847520769458067315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9576711898347179638711543 14365067847520769458067315)
              ·
                refine ⟨21547601771281154187100973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14365067847520769458067315 21547601771281154187100973)
                ·
                  refine ⟨8080350664230432820162865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21547601771281154187100973 8080350664230432820162865)
                  ·
                    refine ⟨6060262998172824615122149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8080350664230432820162865 6060262998172824615122149)
                    ·
                      refine ⟨1136299312157404615335403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6060262998172824615122149 1136299312157404615335403)
                      ·
                        rfl

theorem cell23_2212935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_2212935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2212935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2212935 prefixEnd_2212935 := by exact prefixLift 2212935
  have htrace : WordTrace (prefixWord ++ tailWord_2212935) baseStart_2212935 baseEnd_2212935 := by
    simpa [prefixWord, tailWord_2212935, baseEnd_2212935] using wordTrace_append hprefix tailTrace_2212935
  have hstable : (prefixWord ++ tailWord_2212935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212935).length < 2 ^ (prefixWord ++ tailWord_2212935).sum := by decide
  have hdescent : baseEnd_2212935 < baseStart_2212935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212950 : List Nat := [5, 2, 2, 1, 2, 1, 1, 4, 1, 1, 3]
def baseStart_2212950 : Nat := 118140960795 + 2212950 * 2 ^ 59
def prefixEnd_2212950 : Nat := 4983230072969 + 3 ^ 40 * 2212950 * 2
def baseEnd_2212950 : Nat := 1136307014367222056647835

theorem tailTrace_2212950 : CollatzResearch.WordTrace tailWord_2212950 prefixEnd_2212950 1136307014367222056647835 := by
  unfold tailWord_2212950
  simp only [CollatzResearch.WordTrace]
  refine ⟨5044557333304222913476769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53808611555245044410418869 5044557333304222913476769)
  ·
    refine ⟨3783417999978167185107577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5044557333304222913476769 3783417999978167185107577)
    ·
      refine ⟨2837563499983625388830683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3783417999978167185107577 2837563499983625388830683)
      ·
        refine ⟨4256345249975438083246025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2837563499983625388830683 4256345249975438083246025)
        ·
          refine ⟨3192258937481578562434519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4256345249975438083246025 3192258937481578562434519)
          ·
            refine ⟨4788388406222367843651779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3192258937481578562434519 4788388406222367843651779)
            ·
              refine ⟨7182582609333551765477669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4788388406222367843651779 7182582609333551765477669)
              ·
                refine ⟨1346734239250040956027063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7182582609333551765477669 1346734239250040956027063)
                ·
                  refine ⟨2020101358875061434040595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1346734239250040956027063 2020101358875061434040595)
                  ·
                    refine ⟨3030152038312592151060893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2020101358875061434040595 3030152038312592151060893)
                    ·
                      refine ⟨1136307014367222056647835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3030152038312592151060893 1136307014367222056647835)
                      ·
                        rfl

theorem cell23_2212950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_2212950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2212950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2212950 prefixEnd_2212950 := by exact prefixLift 2212950
  have htrace : WordTrace (prefixWord ++ tailWord_2212950) baseStart_2212950 baseEnd_2212950 := by
    simpa [prefixWord, tailWord_2212950, baseEnd_2212950] using wordTrace_append hprefix tailTrace_2212950
  have hstable : (prefixWord ++ tailWord_2212950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212950).length < 2 ^ (prefixWord ++ tailWord_2212950).sum := by decide
  have hdescent : baseEnd_2212950 < baseStart_2212950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212962 : List Nat := [3, 3, 2, 2, 1, 1, 3, 8]
def baseStart_2212962 : Nat := 118140960795 + 2212962 * 2 ^ 59
def prefixEnd_2212962 : Nat := 4983230072969 + 3 ^ 40 * 2212962 * 2
def baseEnd_2212962 : Nat := 42085673190188000359177

theorem tailTrace_2212962 : CollatzResearch.WordTrace tailWord_2212962 prefixEnd_2212962 42085673190188000359177 := by
  unfold tailWord_2212962
  simp only [CollatzResearch.WordTrace]
  refine ⟨20178338752206023166266285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53808903339216061776710093 20178338752206023166266285)
  ·
    refine ⟨7566877032077258687349857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20178338752206023166266285 7566877032077258687349857)
    ·
      refine ⟨5675157774057944015512393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7566877032077258687349857 5675157774057944015512393)
      ·
        refine ⟨4256368330543458011634295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5675157774057944015512393 4256368330543458011634295)
        ·
          refine ⟨6384552495815187017451443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4256368330543458011634295 6384552495815187017451443)
          ·
            refine ⟨9576828743722780526177165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6384552495815187017451443 9576828743722780526177165)
            ·
              refine ⟨3591310778896042697316437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9576828743722780526177165 3591310778896042697316437)
              ·
                refine ⟨42085673190188000359177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3591310778896042697316437 42085673190188000359177)
                ·
                  rfl

theorem cell23_2212962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 8].length) (baseStart_2212962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2212962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2212962 prefixEnd_2212962 := by exact prefixLift 2212962
  have htrace : WordTrace (prefixWord ++ tailWord_2212962) baseStart_2212962 baseEnd_2212962 := by
    simpa [prefixWord, tailWord_2212962, baseEnd_2212962] using wordTrace_append hprefix tailTrace_2212962
  have hstable : (prefixWord ++ tailWord_2212962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212962).length < 2 ^ (prefixWord ++ tailWord_2212962).sum := by decide
  have hdescent : baseEnd_2212962 < baseStart_2212962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2212972 : List Nat := [2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 3]
def baseStart_2212972 : Nat := 118140960795 + 2212972 * 2 ^ 59
def prefixEnd_2212972 : Nat := 4983230072969 + 3 ^ 40 * 2212972 * 2
def baseEnd_2212972 : Nat := 1136318310941620970572733

theorem tailTrace_2212972 : CollatzResearch.WordTrace tailWord_2212972 prefixEnd_2212972 1136318310941620970572733 := by
  unfold tailWord_2212972
  simp only [CollatzResearch.WordTrace]
  refine ⟨40356859869393932186464585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53809146492525242915286113 40356859869393932186464585)
  ·
    refine ⟨30267644902045449139848439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40356859869393932186464585 30267644902045449139848439)
    ·
      refine ⟨45401467353068173709772659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30267644902045449139848439 45401467353068173709772659)
      ·
        refine ⟨68102201029602260564658989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45401467353068173709772659 68102201029602260564658989)
        ·
          refine ⟨25538325386100847711747121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68102201029602260564658989 25538325386100847711747121)
          ·
            refine ⟨19153744039575635783810341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25538325386100847711747121 19153744039575635783810341)
            ·
              refine ⟨3591327007420431709464439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19153744039575635783810341 3591327007420431709464439)
              ·
                refine ⟨5386990511130647564196659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3591327007420431709464439 5386990511130647564196659)
                ·
                  refine ⟨8080485766695971346294989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5386990511130647564196659 8080485766695971346294989)
                  ·
                    refine ⟨3030182162510989254860621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8080485766695971346294989 3030182162510989254860621)
                    ·
                      refine ⟨1136318310941620970572733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3030182162510989254860621 1136318310941620970572733)
                      ·
                        rfl

theorem cell23_2212972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 3].length) (baseStart_2212972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2212972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2212972 prefixEnd_2212972 := by exact prefixLift 2212972
  have htrace : WordTrace (prefixWord ++ tailWord_2212972) baseStart_2212972 baseEnd_2212972 := by
    simpa [prefixWord, tailWord_2212972, baseEnd_2212972] using wordTrace_append hprefix tailTrace_2212972
  have hstable : (prefixWord ++ tailWord_2212972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2212972).length < 2 ^ (prefixWord ++ tailWord_2212972).sum := by decide
  have hdescent : baseEnd_2212972 < baseStart_2212972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2212972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213006 : List Nat := [4, 1, 1, 3, 2, 1, 3, 2, 2, 1, 3]
def baseStart_2213006 : Nat := 118140960795 + 2213006 * 2 ^ 59
def prefixEnd_2213006 : Nat := 4983230072969 + 3 ^ 40 * 2213006 * 2
def baseEnd_2213006 : Nat := 1136335769283873837547577

theorem tailTrace_2213006 : CollatzResearch.WordTrace tailWord_2213006 prefixEnd_2213006 1136335769283873837547577 := by
  unfold tailWord_2213006
  simp only [CollatzResearch.WordTrace]
  refine ⟨10089369977583086022458359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53809973213776458786444581 10089369977583086022458359)
  ·
    refine ⟨15134054966374629033687539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10089369977583086022458359 15134054966374629033687539)
    ·
      refine ⟨22701082449561943550531309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15134054966374629033687539 22701082449561943550531309)
      ·
        refine ⟨8512905918585728831449241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22701082449561943550531309 8512905918585728831449241)
        ·
          refine ⟨6384679438939296623586931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8512905918585728831449241 6384679438939296623586931)
          ·
            refine ⟨9577019158408944935380397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6384679438939296623586931 9577019158408944935380397)
            ·
              refine ⟨3591382184403354350767649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9577019158408944935380397 3591382184403354350767649)
              ·
                refine ⟨2693536638302515763075737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3591382184403354350767649 2693536638302515763075737)
                ·
                  refine ⟨2020152478726886822306803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2693536638302515763075737 2020152478726886822306803)
                  ·
                    refine ⟨3030228718090330233460205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2020152478726886822306803 3030228718090330233460205)
                    ·
                      refine ⟨1136335769283873837547577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3030228718090330233460205 1136335769283873837547577)
                      ·
                        rfl

theorem cell23_2213006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_2213006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2213006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2213006 prefixEnd_2213006 := by exact prefixLift 2213006
  have htrace : WordTrace (prefixWord ++ tailWord_2213006) baseStart_2213006 baseEnd_2213006 := by
    simpa [prefixWord, tailWord_2213006, baseEnd_2213006] using wordTrace_append hprefix tailTrace_2213006
  have hstable : (prefixWord ++ tailWord_2213006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213006).length < 2 ^ (prefixWord ++ tailWord_2213006).sum := by decide
  have hdescent : baseEnd_2213006 < baseStart_2213006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213023 : List Nat := [1, 1, 2, 6, 2, 1, 3, 1, 2, 1, 3]
def baseStart_2213023 : Nat := 118140960795 + 2213023 * 2 ^ 59
def prefixEnd_2213023 : Nat := 4983230072969 + 3 ^ 40 * 2213023 * 2
def baseEnd_2213023 : Nat := 1136344498455000271034999

theorem tailTrace_2213023 : CollatzResearch.WordTrace tailWord_2213023 prefixEnd_2213023 1136344498455000271034999 := by
  unfold tailWord_2213023
  simp only [CollatzResearch.WordTrace]
  refine ⟨80715579861603100083035723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53810386574402066722023815 80715579861603100083035723)
  ·
    refine ⟨121073369792404650124553585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80715579861603100083035723 121073369792404650124553585)
    ·
      refine ⟨90805027344303487593415189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121073369792404650124553585 90805027344303487593415189)
      ·
        refine ⟨4256485656764225980941337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 90805027344303487593415189 4256485656764225980941337)
        ·
          refine ⟨3192364242573169485706003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4256485656764225980941337 3192364242573169485706003)
          ·
            refine ⟨4788546363859754228559005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3192364242573169485706003 4788546363859754228559005)
            ·
              refine ⟨1795704886447407835709627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4788546363859754228559005 1795704886447407835709627)
              ·
                refine ⟨2693557329671111753564441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1795704886447407835709627 2693557329671111753564441)
                ·
                  refine ⟨2020167997253333815173331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2693557329671111753564441 2020167997253333815173331)
                  ·
                    refine ⟨3030251995880000722759997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2020167997253333815173331 3030251995880000722759997)
                    ·
                      refine ⟨1136344498455000271034999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3030251995880000722759997 1136344498455000271034999)
                      ·
                        rfl

theorem cell23_2213023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_2213023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2213023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2213023 prefixEnd_2213023 := by exact prefixLift 2213023
  have htrace : WordTrace (prefixWord ++ tailWord_2213023) baseStart_2213023 baseEnd_2213023 := by
    simpa [prefixWord, tailWord_2213023, baseEnd_2213023] using wordTrace_append hprefix tailTrace_2213023
  have hstable : (prefixWord ++ tailWord_2213023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213023).length < 2 ^ (prefixWord ++ tailWord_2213023).sum := by decide
  have hdescent : baseEnd_2213023 < baseStart_2213023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213029 : List Nat := [1, 3, 1, 2, 1, 4, 3, 1, 1, 4, 2]
def baseStart_2213029 : Nat := 118140960795 + 2213029 * 2 ^ 59
def prefixEnd_2213029 : Nat := 4983230072969 + 3 ^ 40 * 2213029 * 2
def baseEnd_2213029 : Nat := 1136347579338927247559971

theorem tailTrace_2213029 : CollatzResearch.WordTrace tailWord_2213029 prefixEnd_2213029 1136347579338927247559971 := by
  unfold tailWord_2213029
  simp only [CollatzResearch.WordTrace]
  refine ⟨80715798699581363107754141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53810532466387575405169427 80715798699581363107754141)
  ·
    refine ⟨30268424512343011165407803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80715798699581363107754141 30268424512343011165407803)
    ·
      refine ⟨45402636768514516748111705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30268424512343011165407803 45402636768514516748111705)
      ·
        refine ⟨34051977576385887561083779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45402636768514516748111705 34051977576385887561083779)
        ·
          refine ⟨51077966364578831341625669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34051977576385887561083779 51077966364578831341625669)
          ·
            refine ⟨9577118693358530876554813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51077966364578831341625669 9577118693358530876554813)
            ·
              refine ⟨3591419510009449078708055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9577118693358530876554813 3591419510009449078708055)
              ·
                refine ⟨5387129265014173618062083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3591419510009449078708055 5387129265014173618062083)
                ·
                  refine ⟨8080693897521260427093125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5387129265014173618062083 8080693897521260427093125)
                  ·
                    refine ⟨1515130105785236330079961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8080693897521260427093125 1515130105785236330079961)
                    ·
                      refine ⟨1136347579338927247559971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1515130105785236330079961 1136347579338927247559971)
                      ·
                        rfl

theorem cell23_2213029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 4, 2].length) (baseStart_2213029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2213029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2213029 prefixEnd_2213029 := by exact prefixLift 2213029
  have htrace : WordTrace (prefixWord ++ tailWord_2213029) baseStart_2213029 baseEnd_2213029 := by
    simpa [prefixWord, tailWord_2213029, baseEnd_2213029] using wordTrace_append hprefix tailTrace_2213029
  have hstable : (prefixWord ++ tailWord_2213029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213029).length < 2 ^ (prefixWord ++ tailWord_2213029).sum := by decide
  have hdescent : baseEnd_2213029 < baseStart_2213029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213075 : List Nat := [1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 5]
def baseStart_2213075 : Nat := 118140960795 + 2213075 * 2 ^ 59
def prefixEnd_2213075 : Nat := 4983230072969 + 3 ^ 40 * 2213075 * 2
def baseEnd_2213075 : Nat := 1136371199449034067584759

theorem tailTrace_2213075 : CollatzResearch.WordTrace tailWord_2213075 prefixEnd_2213075 1136371199449034067584759 := by
  unfold tailWord_2213075
  simp only [CollatzResearch.WordTrace]
  refine ⟨80717476457414712963928679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53811650971609808642619119 80717476457414712963928679)
  ·
    refine ⟨121076214686122069445893019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80717476457414712963928679 121076214686122069445893019)
    ·
      refine ⟨181614322029183104168839529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121076214686122069445893019 181614322029183104168839529)
      ·
        refine ⟨136210741521887328126629647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181614322029183104168839529 136210741521887328126629647)
        ·
          refine ⟨204316112282830992189944471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136210741521887328126629647 204316112282830992189944471)
          ·
            refine ⟨306474168424246488284916707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204316112282830992189944471 306474168424246488284916707)
            ·
              refine ⟨459711252636369732427375061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 306474168424246488284916707 459711252636369732427375061)
              ·
                refine ⟨10774482483664915603766603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 459711252636369732427375061 10774482483664915603766603)
                ·
                  refine ⟨16161723725497373405649905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10774482483664915603766603 16161723725497373405649905)
                  ·
                    refine ⟨12121292794123030054237429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16161723725497373405649905 12121292794123030054237429)
                    ·
                      refine ⟨1136371199449034067584759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12121292794123030054237429 1136371199449034067584759)
                      ·
                        rfl

theorem cell23_2213075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 5].length) (baseStart_2213075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2213075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2213075 prefixEnd_2213075 := by exact prefixLift 2213075
  have htrace : WordTrace (prefixWord ++ tailWord_2213075) baseStart_2213075 baseEnd_2213075 := by
    simpa [prefixWord, tailWord_2213075, baseEnd_2213075] using wordTrace_append hprefix tailTrace_2213075
  have hstable : (prefixWord ++ tailWord_2213075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213075).length < 2 ^ (prefixWord ++ tailWord_2213075).sum := by decide
  have hdescent : baseEnd_2213075 < baseStart_2213075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213080 : List Nat := [2, 1, 2, 2, 5, 2, 2, 1, 2, 2, 2]
def baseStart_2213080 : Nat := 118140960795 + 2213080 * 2 ^ 59
def prefixEnd_2213080 : Nat := 4983230072969 + 3 ^ 40 * 2213080 * 2
def baseEnd_2213080 : Nat := 1136373766852306548022237

theorem tailTrace_2213080 : CollatzResearch.WordTrace tailWord_2213080 prefixEnd_2213080 1136373766852306548022237 := by
  unfold tailWord_2213080
  simp only [CollatzResearch.WordTrace]
  refine ⟨40358829411198299408930347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53811772548264399211907129 40358829411198299408930347)
  ·
    refine ⟨60538244116797449113395521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40358829411198299408930347 60538244116797449113395521)
    ·
      refine ⟨45403683087598086835046641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60538244116797449113395521 45403683087598086835046641)
      ·
        refine ⟨34052762315698565126284981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45403683087598086835046641 34052762315698565126284981)
        ·
          refine ⟨3192446467096740480589217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34052762315698565126284981 3192446467096740480589217)
          ·
            refine ⟨2394334850322555360441913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3192446467096740480589217 2394334850322555360441913)
            ·
              refine ⟨1795751137741916520331435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2394334850322555360441913 1795751137741916520331435)
              ·
                refine ⟨2693626706612874780497153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1795751137741916520331435 2693626706612874780497153)
                ·
                  refine ⟨2020220029959656085372865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2693626706612874780497153 2020220029959656085372865)
                  ·
                    refine ⟨1515165022469742064029649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2020220029959656085372865 1515165022469742064029649)
                    ·
                      refine ⟨1136373766852306548022237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1515165022469742064029649 1136373766852306548022237)
                      ·
                        rfl

theorem cell23_2213080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 1, 2, 2, 2].length) (baseStart_2213080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2213080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2213080 prefixEnd_2213080 := by exact prefixLift 2213080
  have htrace : WordTrace (prefixWord ++ tailWord_2213080) baseStart_2213080 baseEnd_2213080 := by
    simpa [prefixWord, tailWord_2213080, baseEnd_2213080] using wordTrace_append hprefix tailTrace_2213080
  have hstable : (prefixWord ++ tailWord_2213080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213080).length < 2 ^ (prefixWord ++ tailWord_2213080).sum := by decide
  have hdescent : baseEnd_2213080 < baseStart_2213080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213102 : List Nat := [4, 1, 2, 1, 1, 1, 2, 3, 1, 3, 4]
def baseStart_2213102 : Nat := 118140960795 + 2213102 * 2 ^ 59
def prefixEnd_2213102 : Nat := 4983230072969 + 3 ^ 40 * 2213102 * 2
def baseEnd_2213102 : Nat := 1136385063426705461947135

theorem tailTrace_2213102 : CollatzResearch.WordTrace tailWord_2213102 prefixEnd_2213102 1136385063426705461947135 := by
  unfold tailWord_2213102
  simp only [CollatzResearch.WordTrace]
  refine ⟨10089807653539612071895195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53812307485544597716774373 10089807653539612071895195)
  ·
    refine ⟨15134711480309418107842793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10089807653539612071895195 15134711480309418107842793)
    ·
      refine ⟨11351033610232063580882095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15134711480309418107842793 11351033610232063580882095)
      ·
        refine ⟨17026550415348095371323143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11351033610232063580882095 17026550415348095371323143)
        ·
          refine ⟨25539825623022143056984715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17026550415348095371323143 25539825623022143056984715)
          ·
            refine ⟨38309738434533214585477073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25539825623022143056984715 38309738434533214585477073)
            ·
              refine ⟨28732303825899910939107805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38309738434533214585477073 28732303825899910939107805)
              ·
                refine ⟨10774613934712466602165427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28732303825899910939107805 10774613934712466602165427)
                ·
                  refine ⟨16161920902068699903248141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10774613934712466602165427 16161920902068699903248141)
                  ·
                    refine ⟨6060720338275762463718053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16161920902068699903248141 6060720338275762463718053)
                    ·
                      refine ⟨1136385063426705461947135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6060720338275762463718053 1136385063426705461947135)
                      ·
                        rfl

theorem cell23_2213102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_2213102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2213102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2213102 prefixEnd_2213102 := by exact prefixLift 2213102
  have htrace : WordTrace (prefixWord ++ tailWord_2213102) baseStart_2213102 baseEnd_2213102 := by
    simpa [prefixWord, tailWord_2213102, baseEnd_2213102] using wordTrace_append hprefix tailTrace_2213102
  have hstable : (prefixWord ++ tailWord_2213102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213102).length < 2 ^ (prefixWord ++ tailWord_2213102).sum := by decide
  have hdescent : baseEnd_2213102 < baseStart_2213102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213150 : List Nat := [4, 3, 2, 1, 3, 1, 1, 1, 2, 5]
def baseStart_2213150 : Nat := 118140960795 + 2213150 * 2 ^ 59
def prefixEnd_2213150 : Nat := 4983230072969 + 3 ^ 40 * 2213150 * 2
def baseEnd_2213150 : Nat := 378803236832707091382305

theorem tailTrace_2213150 : CollatzResearch.WordTrace tailWord_2213150 prefixEnd_2213150 378803236832707091382305 := by
  unfold tailWord_2213150
  simp only [CollatzResearch.WordTrace]
  refine ⟨10090026491517875096613613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53813474621428667181939269 10090026491517875096613613)
  ·
    refine ⟨3783759934319203161230105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10090026491517875096613613 3783759934319203161230105)
    ·
      refine ⟨2837819950739402370922579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3783759934319203161230105 2837819950739402370922579)
      ·
        refine ⟨4256729926109103556383869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2837819950739402370922579 4256729926109103556383869)
        ·
          refine ⟨1596273722290913833643951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4256729926109103556383869 1596273722290913833643951)
          ·
            refine ⟨2394410583436370750465927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1596273722290913833643951 2394410583436370750465927)
            ·
              refine ⟨3591615875154556125698891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2394410583436370750465927 3591615875154556125698891)
              ·
                refine ⟨5387423812731834188548337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3591615875154556125698891 5387423812731834188548337)
                ·
                  refine ⟨4040567859548875641411253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5387423812731834188548337 4040567859548875641411253)
                  ·
                    refine ⟨378803236832707091382305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4040567859548875641411253 378803236832707091382305)
                    ·
                      rfl

theorem cell23_2213150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_2213150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2213150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2213150 prefixEnd_2213150 := by exact prefixLift 2213150
  have htrace : WordTrace (prefixWord ++ tailWord_2213150) baseStart_2213150 baseEnd_2213150 := by
    simpa [prefixWord, tailWord_2213150, baseEnd_2213150] using wordTrace_append hprefix tailTrace_2213150
  have hstable : (prefixWord ++ tailWord_2213150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213150).length < 2 ^ (prefixWord ++ tailWord_2213150).sum := by decide
  have hdescent : baseEnd_2213150 < baseStart_2213150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213209 : List Nat := [1, 2, 1, 2, 2, 2, 3, 4, 1, 1, 4]
def baseStart_2213209 : Nat := 118140960795 + 2213209 * 2 ^ 59
def prefixEnd_2213209 : Nat := 4983230072969 + 3 ^ 40 * 2213209 * 2
def baseEnd_2213209 : Nat := 1136440005856736543309143

theorem tailTrace_2213209 : CollatzResearch.WordTrace tailWord_2213209 prefixEnd_2213209 1136440005856736543309143 := by
  unfold tailWord_2213209
  simp only [CollatzResearch.WordTrace]
  refine ⟨80722363838929253849306681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53814909225952835899537787 80722363838929253849306681)
  ·
    refine ⟨60541772879196940386980011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80722363838929253849306681 60541772879196940386980011)
    ·
      refine ⟨90812659318795410580470017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60541772879196940386980011 90812659318795410580470017)
      ·
        refine ⟨68109494489096557935352513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90812659318795410580470017 68109494489096557935352513)
        ·
          refine ⟨51082120866822418451514385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68109494489096557935352513 51082120866822418451514385)
          ·
            refine ⟨38311590650116813838635789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51082120866822418451514385 38311590650116813838635789)
            ·
              refine ⟨14366846493793805189488421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38311590650116813838635789 14366846493793805189488421)
              ·
                refine ⟨2693783717586338473029079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14366846493793805189488421 2693783717586338473029079)
                ·
                  refine ⟨4040675576379507709543619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2693783717586338473029079 4040675576379507709543619)
                  ·
                    refine ⟨6061013364569261564315429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4040675576379507709543619 6061013364569261564315429)
                    ·
                      refine ⟨1136440005856736543309143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6061013364569261564315429 1136440005856736543309143)
                      ·
                        rfl

theorem cell23_2213209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 4, 1, 1, 4].length) (baseStart_2213209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2213209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2213209 prefixEnd_2213209 := by exact prefixLift 2213209
  have htrace : WordTrace (prefixWord ++ tailWord_2213209) baseStart_2213209 baseEnd_2213209 := by
    simpa [prefixWord, tailWord_2213209, baseEnd_2213209] using wordTrace_append hprefix tailTrace_2213209
  have hstable : (prefixWord ++ tailWord_2213209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213209).length < 2 ^ (prefixWord ++ tailWord_2213209).sum := by decide
  have hdescent : baseEnd_2213209 < baseStart_2213209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213219 : List Nat := [1, 1, 1, 5, 2, 2, 1, 2, 4, 4]
def baseStart_2213219 : Nat := 118140960795 + 2213219 * 2 ^ 59
def prefixEnd_2213219 : Nat := 4983230072969 + 3 ^ 40 * 2213219 * 2
def baseEnd_2213219 : Nat := 378815046887760501394699

theorem tailTrace_2213219 : CollatzResearch.WordTrace tailWord_2213219 prefixEnd_2213219 378815046887760501394699 := by
  unfold tailWord_2213219
  simp only [CollatzResearch.WordTrace]
  refine ⟨80722728568893025557170711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53815152379262017038113807 80722728568893025557170711)
  ·
    refine ⟨121084092853339538335756067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80722728568893025557170711 121084092853339538335756067)
    ·
      refine ⟨181626139280009307503634101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121084092853339538335756067 181626139280009307503634101)
      ·
        refine ⟨17027450557500872578465697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 181626139280009307503634101 17027450557500872578465697)
        ·
          refine ⟨12770587918125654433849273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17027450557500872578465697 12770587918125654433849273)
          ·
            refine ⟨9577940938594240825386955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12770587918125654433849273 9577940938594240825386955)
            ·
              refine ⟨14366911407891361238080433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9577940938594240825386955 14366911407891361238080433)
              ·
                refine ⟨10775183555918520928560325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14366911407891361238080433 10775183555918520928560325)
                ·
                  refine ⟨2020346916734722674105061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10775183555918520928560325 2020346916734722674105061)
                  ·
                    refine ⟨378815046887760501394699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2020346916734722674105061 378815046887760501394699)
                    ·
                      rfl

theorem cell23_2213219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 4, 4].length) (baseStart_2213219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2213219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2213219 prefixEnd_2213219 := by exact prefixLift 2213219
  have htrace : WordTrace (prefixWord ++ tailWord_2213219) baseStart_2213219 baseEnd_2213219 := by
    simpa [prefixWord, tailWord_2213219, baseEnd_2213219] using wordTrace_append hprefix tailTrace_2213219
  have hstable : (prefixWord ++ tailWord_2213219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213219).length < 2 ^ (prefixWord ++ tailWord_2213219).sum := by decide
  have hdescent : baseEnd_2213219 < baseStart_2213219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213220 : List Nat := [2, 3, 1, 1, 3, 4, 1, 3, 1, 1, 3]
def baseStart_2213220 : Nat := 118140960795 + 2213220 * 2 ^ 59
def prefixEnd_2213220 : Nat := 4983230072969 + 3 ^ 40 * 2213220 * 2
def baseEnd_2213220 : Nat := 1136445654143936000271593

theorem tailTrace_2213220 : CollatzResearch.WordTrace tailWord_2213220 prefixEnd_2213220 1136445654143936000271593 := by
  unfold tailWord_2213220
  simp only [CollatzResearch.WordTrace]
  refine ⟨40361382520944701363978557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53815176694592935151971409 40361382520944701363978557)
  ·
    refine ⟨15135518445354263011491959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40361382520944701363978557 15135518445354263011491959)
    ·
      refine ⟨22703277668031394517237939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15135518445354263011491959 22703277668031394517237939)
      ·
        refine ⟨34054916502047091775856909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22703277668031394517237939 34054916502047091775856909)
        ·
          refine ⟨12770593688267659415946341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34054916502047091775856909 12770593688267659415946341)
          ·
            refine ⟨2394486316550186140489939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12770593688267659415946341 2394486316550186140489939)
            ·
              refine ⟨3591729474825279210734909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2394486316550186140489939 3591729474825279210734909)
              ·
                refine ⟨1346898553059479704025591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3591729474825279210734909 1346898553059479704025591)
                ·
                  refine ⟨2020347829589219556038387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1346898553059479704025591 2020347829589219556038387)
                  ·
                    refine ⟨3030521744383829334057581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2020347829589219556038387 3030521744383829334057581)
                    ·
                      refine ⟨1136445654143936000271593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3030521744383829334057581 1136445654143936000271593)
                      ·
                        rfl

theorem cell23_2213220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 3, 1, 1, 3].length) (baseStart_2213220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2213220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2213220 prefixEnd_2213220 := by exact prefixLift 2213220
  have htrace : WordTrace (prefixWord ++ tailWord_2213220) baseStart_2213220 baseEnd_2213220 := by
    simpa [prefixWord, tailWord_2213220, baseEnd_2213220] using wordTrace_append hprefix tailTrace_2213220
  have hstable : (prefixWord ++ tailWord_2213220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213220).length < 2 ^ (prefixWord ++ tailWord_2213220).sum := by decide
  have hdescent : baseEnd_2213220 < baseStart_2213220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213229 : List Nat := [1, 5, 1, 1, 1, 3, 1, 3, 1, 1, 5]
def baseStart_2213229 : Nat := 118140960795 + 2213229 * 2 ^ 59
def prefixEnd_2213229 : Nat := 4983230072969 + 3 ^ 40 * 2213229 * 2
def baseEnd_2213229 : Nat := 1136450275469826465059051

theorem tailTrace_2213229 : CollatzResearch.WordTrace tailWord_2213229 prefixEnd_2213229 1136450275469826465059051 := by
  unfold tailWord_2213229
  simp only [CollatzResearch.WordTrace]
  refine ⟨80723093298856797265034741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53815395532571198176689827 80723093298856797265034741)
  ·
    refine ⟨7567789996767824743597007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80723093298856797265034741 7567789996767824743597007)
    ·
      refine ⟨11351684995151737115395511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7567789996767824743597007 11351684995151737115395511)
      ·
        refine ⟨17027527492727605673093267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11351684995151737115395511 17027527492727605673093267)
        ·
          refine ⟨25541291239091408509639901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17027527492727605673093267 25541291239091408509639901)
          ·
            refine ⟨9577984214659278191114963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25541291239091408509639901 9577984214659278191114963)
            ·
              refine ⟨14366976321988917286672445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9577984214659278191114963 14366976321988917286672445)
              ·
                refine ⟨5387616120745843982502167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14366976321988917286672445 5387616120745843982502167)
                ·
                  refine ⟨8081424181118765973753251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5387616120745843982502167 8081424181118765973753251)
                  ·
                    refine ⟨12122136271678148960629877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8081424181118765973753251 12122136271678148960629877)
                    ·
                      refine ⟨1136450275469826465059051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12122136271678148960629877 1136450275469826465059051)
                      ·
                        rfl

theorem cell23_2213229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_2213229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2213229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2213229 prefixEnd_2213229 := by exact prefixLift 2213229
  have htrace : WordTrace (prefixWord ++ tailWord_2213229) baseStart_2213229 baseEnd_2213229 := by
    simpa [prefixWord, tailWord_2213229, baseEnd_2213229] using wordTrace_append hprefix tailTrace_2213229
  have hstable : (prefixWord ++ tailWord_2213229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213229).length < 2 ^ (prefixWord ++ tailWord_2213229).sum := by decide
  have hdescent : baseEnd_2213229 < baseStart_2213229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213230 : List Nat := [4, 1, 2, 4, 1, 1, 1, 2, 2, 3, 2]
def baseStart_2213230 : Nat := 118140960795 + 2213230 * 2 ^ 59
def prefixEnd_2213230 : Nat := 4983230072969 + 3 ^ 40 * 2213230 * 2
def baseEnd_2213230 : Nat := 1136450788950480961146547

theorem tailTrace_2213230 : CollatzResearch.WordTrace tailWord_2213230 prefixEnd_2213230 1136450788950480961146547 := by
  unfold tailWord_2213230
  simp only [CollatzResearch.WordTrace]
  refine ⟨10090391221481646804477643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53815419847902116290547429 10090391221481646804477643)
  ·
    refine ⟨15135586832222470206716465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10090391221481646804477643 15135586832222470206716465)
    ·
      refine ⟨11351690124166852655037349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15135586832222470206716465 11351690124166852655037349)
      ·
        refine ⟨2128441898281284872819503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11351690124166852655037349 2128441898281284872819503)
        ·
          refine ⟨3192662847421927309229255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2128441898281284872819503 3192662847421927309229255)
          ·
            refine ⟨4788994271132890963843883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3192662847421927309229255 4788994271132890963843883)
            ·
              refine ⟨7183491406699336445765825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4788994271132890963843883 7183491406699336445765825)
              ·
                refine ⟨5387618555024502334324369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7183491406699336445765825 5387618555024502334324369)
                ·
                  refine ⟨4040713916268376750743277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5387618555024502334324369 4040713916268376750743277)
                  ·
                    refine ⟨1515267718600641281528729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4040713916268376750743277 1515267718600641281528729)
                    ·
                      refine ⟨1136450788950480961146547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1515267718600641281528729 1136450788950480961146547)
                      ·
                        rfl

theorem cell23_2213230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_2213230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2213230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2213230 prefixEnd_2213230 := by exact prefixLift 2213230
  have htrace : WordTrace (prefixWord ++ tailWord_2213230) baseStart_2213230 baseEnd_2213230 := by
    simpa [prefixWord, tailWord_2213230, baseEnd_2213230] using wordTrace_append hprefix tailTrace_2213230
  have hstable : (prefixWord ++ tailWord_2213230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213230).length < 2 ^ (prefixWord ++ tailWord_2213230).sum := by decide
  have hdescent : baseEnd_2213230 < baseStart_2213230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213237 : List Nat := [1, 3, 4, 1, 3, 1, 3, 2, 1, 1, 3]
def baseStart_2213237 : Nat := 118140960795 + 2213237 * 2 ^ 59
def prefixEnd_2213237 : Nat := 4983230072969 + 3 ^ 40 * 2213237 * 2
def baseEnd_2213237 : Nat := 1136454383315062433759015

theorem tailTrace_2213237 : CollatzResearch.WordTrace tailWord_2213237 prefixEnd_2213237 1136454383315062433759015 := by
  unfold tailWord_2213237
  simp only [CollatzResearch.WordTrace]
  refine ⟨80723385082827814631325965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53815590055218543087550643 80723385082827814631325965)
  ·
    refine ⟨30271269406060430486747237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80723385082827814631325965 30271269406060430486747237)
    ·
      refine ⟨5675863013636330716265107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30271269406060430486747237 5675863013636330716265107)
      ·
        refine ⟨8513794520454496074397661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5675863013636330716265107 8513794520454496074397661)
        ·
          refine ⟨3192672945170436027899123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8513794520454496074397661 3192672945170436027899123)
          ·
            refine ⟨4789009417755654041848685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3192672945170436027899123 4789009417755654041848685)
            ·
              refine ⟨1795878531658370265693257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4789009417755654041848685 1795878531658370265693257)
              ·
                refine ⟨1346908898743777699269943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1795878531658370265693257 1346908898743777699269943)
                ·
                  refine ⟨2020363348115666548904915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1346908898743777699269943 2020363348115666548904915)
                  ·
                    refine ⟨3030545022173499823357373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2020363348115666548904915 3030545022173499823357373)
                    ·
                      refine ⟨1136454383315062433759015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3030545022173499823357373 1136454383315062433759015)
                      ·
                        rfl

theorem cell23_2213237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_2213237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2213237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2213237 prefixEnd_2213237 := by exact prefixLift 2213237
  have htrace : WordTrace (prefixWord ++ tailWord_2213237) baseStart_2213237 baseEnd_2213237 := by
    simpa [prefixWord, tailWord_2213237, baseEnd_2213237] using wordTrace_append hprefix tailTrace_2213237
  have hstable : (prefixWord ++ tailWord_2213237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213237).length < 2 ^ (prefixWord ++ tailWord_2213237).sum := by decide
  have hdescent : baseEnd_2213237 < baseStart_2213237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213259 : List Nat := [1, 1, 1, 1, 4, 3, 2, 3, 1, 3, 3]
def baseStart_2213259 : Nat := 118140960795 + 2213259 * 2 ^ 59
def prefixEnd_2213259 : Nat := 4983230072969 + 3 ^ 40 * 2213259 * 2
def baseEnd_2213259 : Nat := 1136465679889461347683913

theorem tailTrace_2213259 : CollatzResearch.WordTrace tailWord_2213259 prefixEnd_2213259 1136465679889461347683913 := by
  unfold tailWord_2213259
  simp only [CollatzResearch.WordTrace]
  refine ⟨80724187488748112388626831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53816124992498741592417887 80724187488748112388626831)
  ·
    refine ⟨121086281233122168582940247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80724187488748112388626831 121086281233122168582940247)
    ·
      refine ⟨181629421849683252874410371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121086281233122168582940247 181629421849683252874410371)
      ·
        refine ⟨272444132774524879311615557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181629421849683252874410371 272444132774524879311615557)
        ·
          refine ⟨51083274895223414870927917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 272444132774524879311615557 51083274895223414870927917)
          ·
            refine ⟨19156228085708780576597969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51083274895223414870927917 19156228085708780576597969)
            ·
              refine ⟨14367171064281585432448477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19156228085708780576597969 14367171064281585432448477)
              ·
                refine ⟨5387689149105594537168179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14367171064281585432448477 5387689149105594537168179)
                ·
                  refine ⟨8081533723658391805752269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5387689149105594537168179 8081533723658391805752269)
                  ·
                    refine ⟨3030575146371896927157101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8081533723658391805752269 3030575146371896927157101)
                    ·
                      refine ⟨1136465679889461347683913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3030575146371896927157101 1136465679889461347683913)
                      ·
                        rfl

theorem cell23_2213259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 3, 3].length) (baseStart_2213259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2213259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2213259 prefixEnd_2213259 := by exact prefixLift 2213259
  have htrace : WordTrace (prefixWord ++ tailWord_2213259) baseStart_2213259 baseEnd_2213259 := by
    simpa [prefixWord, tailWord_2213259, baseEnd_2213259] using wordTrace_append hprefix tailTrace_2213259
  have hstable : (prefixWord ++ tailWord_2213259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213259).length < 2 ^ (prefixWord ++ tailWord_2213259).sum := by decide
  have hdescent : baseEnd_2213259 < baseStart_2213259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213309 : List Nat := [1, 4, 1, 2, 2, 1, 3, 1, 2, 6]
def baseStart_2213309 : Nat := 118140960795 + 2213309 * 2 ^ 59
def prefixEnd_2213309 : Nat := 4983230072969 + 3 ^ 40 * 2213309 * 2
def baseEnd_2213309 : Nat := 378830451307395384019561

theorem tailTrace_2213309 : CollatzResearch.WordTrace tailWord_2213309 prefixEnd_2213309 378830451307395384019561 := by
  unfold tailWord_2213309
  simp only [CollatzResearch.WordTrace]
  refine ⟨80726011138566970927946981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53817340759044647285297987 80726011138566970927946981)
  ·
    refine ⟨15136127088481307048990059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80726011138566970927946981 15136127088481307048990059)
    ·
      refine ⟨22704190632721960573485089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15136127088481307048990059 22704190632721960573485089)
      ·
        refine ⟨17028142974541470430113817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22704190632721960573485089 17028142974541470430113817)
        ·
          refine ⟨12771107230906102822585363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17028142974541470430113817 12771107230906102822585363)
          ·
            refine ⟨19156660846359154233878045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12771107230906102822585363 19156660846359154233878045)
            ·
              refine ⟨7183747817384682837704267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19156660846359154233878045 7183747817384682837704267)
              ·
                refine ⟨10775621726077024256556401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7183747817384682837704267 10775621726077024256556401)
                ·
                  refine ⟨8081716294557768192417301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10775621726077024256556401 8081716294557768192417301)
                  ·
                    refine ⟨378830451307395384019561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8081716294557768192417301 378830451307395384019561)
                    ·
                      rfl

theorem cell23_2213309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 6].length) (baseStart_2213309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2213309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2213309 prefixEnd_2213309 := by exact prefixLift 2213309
  have htrace : WordTrace (prefixWord ++ tailWord_2213309) baseStart_2213309 baseEnd_2213309 := by
    simpa [prefixWord, tailWord_2213309, baseEnd_2213309] using wordTrace_append hprefix tailTrace_2213309
  have hstable : (prefixWord ++ tailWord_2213309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213309).length < 2 ^ (prefixWord ++ tailWord_2213309).sum := by decide
  have hdescent : baseEnd_2213309 < baseStart_2213309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213319 : List Nat := [1, 1, 4, 1, 1, 3, 1, 2, 2, 4, 3]
def baseStart_2213319 : Nat := 118140960795 + 2213319 * 2 ^ 59
def prefixEnd_2213319 : Nat := 4983230072969 + 3 ^ 40 * 2213319 * 2
def baseEnd_2213319 : Nat := 1136496488728731112933637

theorem tailTrace_2213319 : CollatzResearch.WordTrace tailWord_2213319 prefixEnd_2213319 1136496488728731112933637 := by
  unfold tailWord_2213319
  simp only [CollatzResearch.WordTrace]
  refine ⟨80726375868530742635811011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53817583912353828423874007 80726375868530742635811011)
  ·
    refine ⟨121089563802796113953716517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80726375868530742635811011 121089563802796113953716517)
    ·
      refine ⟨22704293213024271366321847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121089563802796113953716517 22704293213024271366321847)
      ·
        refine ⟨34056439819536407049482771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22704293213024271366321847 34056439819536407049482771)
        ·
          refine ⟨51084659729304610574224157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34056439819536407049482771 51084659729304610574224157)
          ·
            refine ⟨19156747398489228965334059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51084659729304610574224157 19156747398489228965334059)
            ·
              refine ⟨28735121097733843448001089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19156747398489228965334059 28735121097733843448001089)
              ·
                refine ⟨21551340823300382586000817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28735121097733843448001089 21551340823300382586000817)
                ·
                  refine ⟨16163505617475286939500613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21551340823300382586000817 16163505617475286939500613)
                  ·
                    refine ⟨3030657303276616301156365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16163505617475286939500613 3030657303276616301156365)
                    ·
                      refine ⟨1136496488728731112933637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3030657303276616301156365 1136496488728731112933637)
                      ·
                        rfl

theorem cell23_2213319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 4, 3].length) (baseStart_2213319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2213319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2213319 prefixEnd_2213319 := by exact prefixLift 2213319
  have htrace : WordTrace (prefixWord ++ tailWord_2213319) baseStart_2213319 baseEnd_2213319 := by
    simpa [prefixWord, tailWord_2213319, baseEnd_2213319] using wordTrace_append hprefix tailTrace_2213319
  have hstable : (prefixWord ++ tailWord_2213319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213319).length < 2 ^ (prefixWord ++ tailWord_2213319).sum := by decide
  have hdescent : baseEnd_2213319 < baseStart_2213319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213333 : List Nat := [1, 3, 2, 3, 1, 1, 2, 2, 4, 2, 2]
def baseStart_2213333 : Nat := 118140960795 + 2213333 * 2 ^ 59
def prefixEnd_2213333 : Nat := 4983230072969 + 3 ^ 40 * 2213333 * 2
def baseEnd_2213333 : Nat := 1136503677457894058158573

theorem tailTrace_2213333 : CollatzResearch.WordTrace tailWord_2213333 prefixEnd_2213333 1136503677457894058158573 := by
  unfold tailWord_2213333
  simp only [CollatzResearch.WordTrace]
  refine ⟨80726886490480023026820653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53817924326986682017880435 80726886490480023026820653)
  ·
    refine ⟨30272582433930008635057745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80726886490480023026820653 30272582433930008635057745)
    ·
      refine ⟨22704436825447506476293309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30272582433930008635057745 22704436825447506476293309)
      ·
        refine ⟨8514163809542814928609991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22704436825447506476293309 8514163809542814928609991)
        ·
          refine ⟨12771245714314222392914987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8514163809542814928609991 12771245714314222392914987)
          ·
            refine ⟨19156868571471333589372481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12771245714314222392914987 19156868571471333589372481)
            ·
              refine ⟨14367651428603500192029361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19156868571471333589372481 14367651428603500192029361)
              ·
                refine ⟨10775738571452625144022021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14367651428603500192029361 10775738571452625144022021)
                ·
                  refine ⟨2020450982147367214504129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10775738571452625144022021 2020450982147367214504129)
                  ·
                    refine ⟨1515338236610525410878097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2020450982147367214504129 1515338236610525410878097)
                    ·
                      refine ⟨1136503677457894058158573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1515338236610525410878097 1136503677457894058158573)
                      ·
                        rfl

theorem cell23_2213333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_2213333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2213333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2213333 prefixEnd_2213333 := by exact prefixLift 2213333
  have htrace : WordTrace (prefixWord ++ tailWord_2213333) baseStart_2213333 baseEnd_2213333 := by
    simpa [prefixWord, tailWord_2213333, baseEnd_2213333] using wordTrace_append hprefix tailTrace_2213333
  have hstable : (prefixWord ++ tailWord_2213333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213333).length < 2 ^ (prefixWord ++ tailWord_2213333).sum := by decide
  have hdescent : baseEnd_2213333 < baseStart_2213333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213390 : List Nat := [4, 1, 1, 2, 4, 2, 1, 3, 5]
def baseStart_2213390 : Nat := 118140960795 + 2213390 * 2 ^ 59
def prefixEnd_2213390 : Nat := 4983230072969 + 3 ^ 40 * 2213390 * 2
def baseEnd_2213390 : Nat := 126281438428355592793979

theorem tailTrace_2213390 : CollatzResearch.WordTrace tailWord_2213390 prefixEnd_2213390 126281438428355592793979 := by
  unfold tailWord_2213390
  simp only [CollatzResearch.WordTrace]
  refine ⟨10091120681409190220205703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53819310300849014507763749 10091120681409190220205703)
  ·
    refine ⟨15136681022113785330308555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10091120681409190220205703 15136681022113785330308555)
    ·
      refine ⟨22705021533170677995462833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15136681022113785330308555 22705021533170677995462833)
      ·
        refine ⟨17028766149878008496597125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22705021533170677995462833 17028766149878008496597125)
        ·
          refine ⟨3192893653102126593111961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17028766149878008496597125 3192893653102126593111961)
          ·
            refine ⟨2394670239826594944833971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3192893653102126593111961 2394670239826594944833971)
            ·
              refine ⟨3592005359739892417250957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2394670239826594944833971 3592005359739892417250957)
              ·
                refine ⟨1347002009902459656469109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3592005359739892417250957 1347002009902459656469109)
                ·
                  refine ⟨126281438428355592793979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1347002009902459656469109 126281438428355592793979)
                  ·
                    rfl

theorem cell23_2213390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 3, 5].length) (baseStart_2213390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2213390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2213390 prefixEnd_2213390 := by exact prefixLift 2213390
  have htrace : WordTrace (prefixWord ++ tailWord_2213390) baseStart_2213390 baseEnd_2213390 := by
    simpa [prefixWord, tailWord_2213390, baseEnd_2213390] using wordTrace_append hprefix tailTrace_2213390
  have hstable : (prefixWord ++ tailWord_2213390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213390).length < 2 ^ (prefixWord ++ tailWord_2213390).sum := by decide
  have hdescent : baseEnd_2213390 < baseStart_2213390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213426 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3]
def baseStart_2213426 : Nat := 118140960795 + 2213426 * 2 ^ 59
def prefixEnd_2213426 : Nat := 4983230072969 + 3 ^ 40 * 2213426 * 2
def baseEnd_2213426 : Nat := 1136551431158762194295645

theorem tailTrace_2213426 : CollatzResearch.WordTrace tailWord_2213426 prefixEnd_2213426 1136551431158762194295645 := by
  unfold tailWord_2213426
  simp only [CollatzResearch.WordTrace]
  refine ⟨20182569619785774977489033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53820185652762066606637421 20182569619785774977489033)
  ·
    refine ⟨15136927214839331233116775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20182569619785774977489033 15136927214839331233116775)
    ·
      refine ⟨22705390822258996849675163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15136927214839331233116775 22705390822258996849675163)
      ·
        refine ⟨34058086233388495274512745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22705390822258996849675163 34058086233388495274512745)
        ·
          refine ⟨25543564675041371455884559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34058086233388495274512745 25543564675041371455884559)
          ·
            refine ⟨38315347012562057183826839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25543564675041371455884559 38315347012562057183826839)
            ·
              refine ⟨57473020518843085775740259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38315347012562057183826839 57473020518843085775740259)
              ·
                refine ⟨86209530778264628663610389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57473020518843085775740259 86209530778264628663610389)
                ·
                  refine ⟨4041071755231154468606737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 86209530778264628663610389 4041071755231154468606737)
                  ·
                    refine ⟨3030803816423365851455053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4041071755231154468606737 3030803816423365851455053)
                    ·
                      refine ⟨1136551431158762194295645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3030803816423365851455053 1136551431158762194295645)
                      ·
                        rfl

theorem cell23_2213426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3].length) (baseStart_2213426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2213426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2213426 prefixEnd_2213426 := by exact prefixLift 2213426
  have htrace : WordTrace (prefixWord ++ tailWord_2213426) baseStart_2213426 baseEnd_2213426 := by
    simpa [prefixWord, tailWord_2213426, baseEnd_2213426] using wordTrace_append hprefix tailTrace_2213426
  have hstable : (prefixWord ++ tailWord_2213426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213426).length < 2 ^ (prefixWord ++ tailWord_2213426).sum := by decide
  have hdescent : baseEnd_2213426 < baseStart_2213426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213473 : List Nat := [1, 2, 3, 1, 1, 3, 2, 3, 3, 1, 3]
def baseStart_2213473 : Nat := 118140960795 + 2213473 * 2 ^ 59
def prefixEnd_2213473 : Nat := 4983230072969 + 3 ^ 40 * 2213473 * 2
def baseEnd_2213473 : Nat := 1136575564749523510407929

theorem tailTrace_2213473 : CollatzResearch.WordTrace tailWord_2213473 prefixEnd_2213473 1136575564749523510407929 := by
  unfold tailWord_2213473
  simp only [CollatzResearch.WordTrace]
  refine ⟨80731992709972826936917073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53821328473315217957944715 80731992709972826936917073)
  ·
    refine ⟨60548994532479620202687805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80731992709972826936917073 60548994532479620202687805)
    ·
      refine ⟨22705872949679857576007927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60548994532479620202687805 22705872949679857576007927)
      ·
        refine ⟨34058809424519786364011891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22705872949679857576007927 34058809424519786364011891)
        ·
          refine ⟨51088214136779679546017837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34058809424519786364011891 51088214136779679546017837)
          ·
            refine ⟨19158080301292379829756689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51088214136779679546017837 19158080301292379829756689)
            ·
              refine ⟨14368560225969284872317517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19158080301292379829756689 14368560225969284872317517)
              ·
                refine ⟨5388210084738481827119069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14368560225969284872317517 5388210084738481827119069)
                ·
                  refine ⟨2020578781776930685169651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5388210084738481827119069 2020578781776930685169651)
                  ·
                    refine ⟨3030868172665396027754477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2020578781776930685169651 3030868172665396027754477)
                    ·
                      refine ⟨1136575564749523510407929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3030868172665396027754477 1136575564749523510407929)
                      ·
                        rfl

theorem cell23_2213473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 3, 1, 3].length) (baseStart_2213473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2213473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2213473 prefixEnd_2213473 := by exact prefixLift 2213473
  have htrace : WordTrace (prefixWord ++ tailWord_2213473) baseStart_2213473 baseEnd_2213473 := by
    simpa [prefixWord, tailWord_2213473, baseEnd_2213473] using wordTrace_append hprefix tailTrace_2213473
  have hstable : (prefixWord ++ tailWord_2213473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213473).length < 2 ^ (prefixWord ++ tailWord_2213473).sum := by decide
  have hdescent : baseEnd_2213473 < baseStart_2213473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213476 : List Nat := [2, 3, 1, 1, 2, 3, 1, 2, 3, 5]
def baseStart_2213476 : Nat := 118140960795 + 2213476 * 2 ^ 59
def prefixEnd_2213476 : Nat := 4983230072969 + 3 ^ 40 * 2213476 * 2
def baseEnd_2213476 : Nat := 378859035063828999556805

theorem tailTrace_2213476 : CollatzResearch.WordTrace tailWord_2213476 prefixEnd_2213476 378859035063828999556805 := by
  unfold tailWord_2213476
  simp only [CollatzResearch.WordTrace]
  refine ⟨40366051064480979224638141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53821401419307972299517521 40366051064480979224638141)
  ·
    refine ⟨15137269149180367209239303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40366051064480979224638141 15137269149180367209239303)
    ·
      refine ⟨22705903723770550813858955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15137269149180367209239303 22705903723770550813858955)
      ·
        refine ⟨34058855585655826220788433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22705903723770550813858955 34058855585655826220788433)
        ·
          refine ⟨25544141689241869665591325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34058855585655826220788433 25544141689241869665591325)
          ·
            refine ⟨9579053133465701124596747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25544141689241869665591325 9579053133465701124596747)
            ·
              refine ⟨14368579700198551686895121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9579053133465701124596747 14368579700198551686895121)
              ·
                refine ⟨10776434775148913765171341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14368579700198551686895121 10776434775148913765171341)
                ·
                  refine ⟨4041163040680842661939253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10776434775148913765171341 4041163040680842661939253)
                  ·
                    refine ⟨378859035063828999556805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4041163040680842661939253 378859035063828999556805)
                    ·
                      rfl

theorem cell23_2213476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 3, 5].length) (baseStart_2213476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2213476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2213476 prefixEnd_2213476 := by exact prefixLift 2213476
  have htrace : WordTrace (prefixWord ++ tailWord_2213476) baseStart_2213476 baseEnd_2213476 := by
    simpa [prefixWord, tailWord_2213476, baseEnd_2213476] using wordTrace_append hprefix tailTrace_2213476
  have hstable : (prefixWord ++ tailWord_2213476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213476).length < 2 ^ (prefixWord ++ tailWord_2213476).sum := by decide
  have hdescent : baseEnd_2213476 < baseStart_2213476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213490 : List Nat := [3, 2, 1, 2, 3, 2, 1, 2, 3, 1, 3]
def baseStart_2213490 : Nat := 118140960795 + 2213490 * 2 ^ 59
def prefixEnd_2213490 : Nat := 4983230072969 + 3 ^ 40 * 2213490 * 2
def baseEnd_2213490 : Nat := 1136584293920649943895351

theorem tailTrace_2213490 : CollatzResearch.WordTrace tailWord_2213490 prefixEnd_2213490 1136584293920649943895351 := by
  unfold tailWord_2213490
  simp only [CollatzResearch.WordTrace]
  refine ⟨20183153187727809710071481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53821741833940825893523949 20183153187727809710071481)
  ·
    refine ⟨15137364890795857282553611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20183153187727809710071481 15137364890795857282553611)
    ·
      refine ⟨22706047336193785923830417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15137364890795857282553611 22706047336193785923830417)
      ·
        refine ⟨17029535502145339442872813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22706047336193785923830417 17029535502145339442872813)
        ·
          refine ⟨6386075813304502291077305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17029535502145339442872813 6386075813304502291077305)
          ·
            refine ⟨4789556859978376718307979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6386075813304502291077305 4789556859978376718307979)
            ·
              refine ⟨7184335289967565077461969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4789556859978376718307979 7184335289967565077461969)
              ·
                refine ⟨5388251467475673808096477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7184335289967565077461969 5388251467475673808096477)
                ·
                  refine ⟨2020594300303377678036179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5388251467475673808096477 2020594300303377678036179)
                  ·
                    refine ⟨3030891450455066517054269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2020594300303377678036179 3030891450455066517054269)
                    ·
                      refine ⟨1136584293920649943895351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3030891450455066517054269 1136584293920649943895351)
                      ·
                        rfl

theorem cell23_2213490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_2213490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2213490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2213490 prefixEnd_2213490 := by exact prefixLift 2213490
  have htrace : WordTrace (prefixWord ++ tailWord_2213490) baseStart_2213490 baseEnd_2213490 := by
    simpa [prefixWord, tailWord_2213490, baseEnd_2213490] using wordTrace_append hprefix tailTrace_2213490
  have hstable : (prefixWord ++ tailWord_2213490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213490).length < 2 ^ (prefixWord ++ tailWord_2213490).sum := by decide
  have hdescent : baseEnd_2213490 < baseStart_2213490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213493 : List Nat := [1, 3, 4, 2, 1, 1, 2, 1, 3, 5]
def baseStart_2213493 : Nat := 118140960795 + 2213493 * 2 ^ 59
def prefixEnd_2213493 : Nat := 4983230072969 + 3 ^ 40 * 2213493 * 2
def baseEnd_2213493 : Nat := 378861944787537810719279

theorem tailTrace_2213493 : CollatzResearch.WordTrace tailWord_2213493 prefixEnd_2213493 378861944787537810719279 := by
  unfold tailWord_2213493
  simp only [CollatzResearch.WordTrace]
  refine ⟨80732722169900370352645133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53821814779933580235096755 80732722169900370352645133)
  ·
    refine ⟨30274770813712638882241925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80732722169900370352645133 30274770813712638882241925)
    ·
      refine ⟨5676519527571119790420361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30274770813712638882241925 5676519527571119790420361)
      ·
        refine ⟨4257389645678339842815271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5676519527571119790420361 4257389645678339842815271)
        ·
          refine ⟨6386084468517509764222907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4257389645678339842815271 6386084468517509764222907)
          ·
            refine ⟨9579126702776264646334361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6386084468517509764222907 9579126702776264646334361)
            ·
              refine ⟨7184345027082198484750771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9579126702776264646334361 7184345027082198484750771)
              ·
                refine ⟨10776517540623297727126157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7184345027082198484750771 10776517540623297727126157)
                ·
                  refine ⟨4041194077733736647672309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10776517540623297727126157 4041194077733736647672309)
                  ·
                    refine ⟨378861944787537810719279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4041194077733736647672309 378861944787537810719279)
                    ·
                      rfl

theorem cell23_2213493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_2213493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2213493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2213493 prefixEnd_2213493 := by exact prefixLift 2213493
  have htrace : WordTrace (prefixWord ++ tailWord_2213493) baseStart_2213493 baseEnd_2213493 := by
    simpa [prefixWord, tailWord_2213493, baseEnd_2213493] using wordTrace_append hprefix tailTrace_2213493
  have hstable : (prefixWord ++ tailWord_2213493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213493).length < 2 ^ (prefixWord ++ tailWord_2213493).sum := by decide
  have hdescent : baseEnd_2213493 < baseStart_2213493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213516 : List Nat := [2, 2, 1, 2, 1, 1, 4, 3, 1, 1, 5]
def baseStart_2213516 : Nat := 118140960795 + 2213516 * 2 ^ 59
def prefixEnd_2213516 : Nat := 4983230072969 + 3 ^ 40 * 2213516 * 2
def baseEnd_2213516 : Nat := 1136597644417666842170231

theorem tailTrace_2213516 : CollatzResearch.WordTrace tailWord_2213516 prefixEnd_2213516 1136597644417666842170231 := by
  unfold tailWord_2213516
  simp only [CollatzResearch.WordTrace]
  refine ⟨40366780524408522640366201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53822374032544696853821601 40366780524408522640366201)
  ·
    refine ⟨30275085393306391980274651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40366780524408522640366201 30275085393306391980274651)
    ·
      refine ⟨45412628089959587970411977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30275085393306391980274651 45412628089959587970411977)
      ·
        refine ⟨34059471067469690977808983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45412628089959587970411977 34059471067469690977808983)
        ·
          refine ⟨51089206601204536466713475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34059471067469690977808983 51089206601204536466713475)
          ·
            refine ⟨76633809901806804700070213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51089206601204536466713475 76633809901806804700070213)
            ·
              refine ⟨14368839356588775881263165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76633809901806804700070213 14368839356588775881263165)
              ·
                refine ⟨5388314758720790955473687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14368839356588775881263165 5388314758720790955473687)
                ·
                  refine ⟨8082472138081186433210531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5388314758720790955473687 8082472138081186433210531)
                  ·
                    refine ⟨12123708207121779649815797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8082472138081186433210531 12123708207121779649815797)
                    ·
                      refine ⟨1136597644417666842170231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12123708207121779649815797 1136597644417666842170231)
                      ·
                        rfl

theorem cell23_2213516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_2213516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2213516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2213516 prefixEnd_2213516 := by exact prefixLift 2213516
  have htrace : WordTrace (prefixWord ++ tailWord_2213516) baseStart_2213516 baseEnd_2213516 := by
    simpa [prefixWord, tailWord_2213516, baseEnd_2213516] using wordTrace_append hprefix tailTrace_2213516
  have hstable : (prefixWord ++ tailWord_2213516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213516).length < 2 ^ (prefixWord ++ tailWord_2213516).sum := by decide
  have hdescent : baseEnd_2213516 < baseStart_2213516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213544 : List Nat := [2, 1, 7, 1, 1, 1, 2, 2, 1, 5]
def baseStart_2213544 : Nat := 118140960795 + 2213544 * 2 ^ 59
def prefixEnd_2213544 : Nat := 4983230072969 + 3 ^ 40 * 2213544 * 2
def baseEnd_2213544 : Nat := 378870673958664244206701

theorem tailTrace_2213544 : CollatzResearch.WordTrace tailWord_2213544 prefixEnd_2213544 378870673958664244206701 := by
  unfold tailWord_2213544
  simp only [CollatzResearch.WordTrace]
  refine ⟨40367291146357803031375843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53823054861810404041834457 40367291146357803031375843)
  ·
    refine ⟨60550936719536704547063765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40367291146357803031375843 60550936719536704547063765)
    ·
      refine ⟨1419162579364141512821807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 60550936719536704547063765 1419162579364141512821807)
      ·
        refine ⟨2128743869046212269232711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1419162579364141512821807 2128743869046212269232711)
        ·
          refine ⟨3193115803569318403849067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2128743869046212269232711 3193115803569318403849067)
          ·
            refine ⟨4789673705353977605773601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3193115803569318403849067 4789673705353977605773601)
            ·
              refine ⟨3592255279015483204330201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4789673705353977605773601 3592255279015483204330201)
              ·
                refine ⟨2694191459261612403247651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3592255279015483204330201 2694191459261612403247651)
                ·
                  refine ⟨4041287188892418604871477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2694191459261612403247651 4041287188892418604871477)
                  ·
                    refine ⟨378870673958664244206701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4041287188892418604871477 378870673958664244206701)
                    ·
                      rfl

theorem cell23_2213544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_2213544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2213544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2213544 prefixEnd_2213544 := by exact prefixLift 2213544
  have htrace : WordTrace (prefixWord ++ tailWord_2213544) baseStart_2213544 baseEnd_2213544 := by
    simpa [prefixWord, tailWord_2213544, baseEnd_2213544] using wordTrace_append hprefix tailTrace_2213544
  have hstable : (prefixWord ++ tailWord_2213544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213544).length < 2 ^ (prefixWord ++ tailWord_2213544).sum := by decide
  have hdescent : baseEnd_2213544 < baseStart_2213544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213564 : List Nat := [2, 2, 2, 3, 1, 2, 3, 3, 1, 2, 2]
def baseStart_2213564 : Nat := 118140960795 + 2213564 * 2 ^ 59
def prefixEnd_2213564 : Nat := 4983230072969 + 3 ^ 40 * 2213564 * 2
def baseEnd_2213564 : Nat := 1136622291489082654370011

theorem tailTrace_2213564 : CollatzResearch.WordTrace tailWord_2213564 prefixEnd_2213564 1136622291489082654370011 := by
  unfold tailWord_2213564
  simp only [CollatzResearch.WordTrace]
  refine ⟨40367655876321574739239873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53823541168428766318986497 40367655876321574739239873)
  ·
    refine ⟨30275741907241181054429905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40367655876321574739239873 30275741907241181054429905)
    ·
      refine ⟨22706806430430885790822429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30275741907241181054429905 22706806430430885790822429)
      ·
        refine ⟨8515052411411582171558411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22706806430430885790822429 8515052411411582171558411)
        ·
          refine ⟨12772578617117373257337617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8515052411411582171558411 12772578617117373257337617)
          ·
            refine ⟨9579433962838029943003213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12772578617117373257337617 9579433962838029943003213)
            ·
              refine ⟨3592287736064261228626205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9579433962838029943003213 3592287736064261228626205)
              ·
                refine ⟨1347107901024097960734827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3592287736064261228626205 1347107901024097960734827)
                ·
                  refine ⟨2020661851536146941102241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1347107901024097960734827 2020661851536146941102241)
                  ·
                    refine ⟨1515496388652110205826681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2020661851536146941102241 1515496388652110205826681)
                    ·
                      refine ⟨1136622291489082654370011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1515496388652110205826681 1136622291489082654370011)
                      ·
                        rfl

theorem cell23_2213564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_2213564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2213564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2213564 prefixEnd_2213564 := by exact prefixLift 2213564
  have htrace : WordTrace (prefixWord ++ tailWord_2213564) baseStart_2213564 baseEnd_2213564 := by
    simpa [prefixWord, tailWord_2213564, baseEnd_2213564] using wordTrace_append hprefix tailTrace_2213564
  have hstable : (prefixWord ++ tailWord_2213564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213564).length < 2 ^ (prefixWord ++ tailWord_2213564).sum := by decide
  have hdescent : baseEnd_2213564 < baseStart_2213564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213576 : List Nat := [2, 1, 3, 1, 2, 2, 1, 2, 2, 2, 5]
def baseStart_2213576 : Nat := 118140960795 + 2213576 * 2 ^ 59
def prefixEnd_2213576 : Nat := 4983230072969 + 3 ^ 40 * 2213576 * 2
def baseEnd_2213576 : Nat := 1136628453256936607419955

theorem tailTrace_2213576 : CollatzResearch.WordTrace tailWord_2213576 prefixEnd_2213576 1136628453256936607419955 := by
  unfold tailWord_2213576
  simp only [CollatzResearch.WordTrace]
  refine ⟨40367874714299837763958291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53823832952399783685277721 40367874714299837763958291)
  ·
    refine ⟨60551812071449756645937437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40367874714299837763958291 60551812071449756645937437)
    ·
      refine ⟨22706929526793658742226539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60551812071449756645937437 22706929526793658742226539)
      ·
        refine ⟨34060394290190488113339809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22706929526793658742226539 34060394290190488113339809)
        ·
          refine ⟨25545295717642866085004857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34060394290190488113339809 25545295717642866085004857)
          ·
            refine ⟨19158971788232149563753643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25545295717642866085004857 19158971788232149563753643)
            ·
              refine ⟨28738457682348224345630465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19158971788232149563753643 28738457682348224345630465)
              ·
                refine ⟨21553843261761168259222849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28738457682348224345630465 21553843261761168259222849)
                ·
                  refine ⟨16165382446320876194417137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21553843261761168259222849 16165382446320876194417137)
                  ·
                    refine ⟨12124036834740657145812853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16165382446320876194417137 12124036834740657145812853)
                    ·
                      refine ⟨1136628453256936607419955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12124036834740657145812853 1136628453256936607419955)
                      ·
                        rfl

theorem cell23_2213576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_2213576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2213576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2213576 prefixEnd_2213576 := by exact prefixLift 2213576
  have htrace : WordTrace (prefixWord ++ tailWord_2213576) baseStart_2213576 baseEnd_2213576 := by
    simpa [prefixWord, tailWord_2213576, baseEnd_2213576] using wordTrace_append hprefix tailTrace_2213576
  have hstable : (prefixWord ++ tailWord_2213576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213576).length < 2 ^ (prefixWord ++ tailWord_2213576).sum := by decide
  have hdescent : baseEnd_2213576 < baseStart_2213576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213581 : List Nat := [1, 6, 2, 1, 1, 3, 1, 1, 3, 2, 2]
def baseStart_2213581 : Nat := 118140960795 + 2213581 * 2 ^ 59
def prefixEnd_2213581 : Nat := 4983230072969 + 3 ^ 40 * 2213581 * 2
def baseEnd_2213581 : Nat := 1136631020660209087857433

theorem tailTrace_2213581 : CollatzResearch.WordTrace tailWord_2213581 prefixEnd_2213581 1136631020660209087857433 := by
  unfold tailWord_2213581
  simp only [CollatzResearch.WordTrace]
  refine ⟨80735931793581561381848597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53823954529054374254565731 80735931793581561381848597)
  ·
    refine ⟨3784496802824135689774153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 80735931793581561381848597 3784496802824135689774153)
    ·
      refine ⟨2838372602118101767330615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3784496802824135689774153 2838372602118101767330615)
      ·
        refine ⟨4257558903177152650995923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2838372602118101767330615 4257558903177152650995923)
        ·
          refine ⟨6386338354765728976493885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4257558903177152650995923 6386338354765728976493885)
          ·
            refine ⟨2394876883037148366185207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6386338354765728976493885 2394876883037148366185207)
            ·
              refine ⟨3592315324555722549277811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2394876883037148366185207 3592315324555722549277811)
              ·
                refine ⟨5388472986833583823916717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3592315324555722549277811 5388472986833583823916717)
                ·
                  refine ⟨2020677370062593933968769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5388472986833583823916717 2020677370062593933968769)
                  ·
                    refine ⟨1515508027546945450476577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2020677370062593933968769 1515508027546945450476577)
                    ·
                      refine ⟨1136631020660209087857433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1515508027546945450476577 1136631020660209087857433)
                      ·
                        rfl

theorem cell23_2213581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_2213581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2213581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2213581 prefixEnd_2213581 := by exact prefixLift 2213581
  have htrace : WordTrace (prefixWord ++ tailWord_2213581) baseStart_2213581 baseEnd_2213581 := by
    simpa [prefixWord, tailWord_2213581, baseEnd_2213581] using wordTrace_append hprefix tailTrace_2213581
  have hstable : (prefixWord ++ tailWord_2213581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213581).length < 2 ^ (prefixWord ++ tailWord_2213581).sum := by decide
  have hdescent : baseEnd_2213581 < baseStart_2213581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213616 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 4]
def baseStart_2213616 : Nat := 118140960795 + 2213616 * 2 ^ 59
def prefixEnd_2213616 : Nat := 4983230072969 + 3 ^ 40 * 2213616 * 2
def baseEnd_2213616 : Nat := 1136648992483116450919771

theorem tailTrace_2213616 : CollatzResearch.WordTrace tailWord_2213616 prefixEnd_2213616 1136648992483116450919771 := by
  unfold tailWord_2213616
  simp only [CollatzResearch.WordTrace]
  refine ⟨40368604174227381179686351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53824805565636508239581801 40368604174227381179686351)
  ·
    refine ⟨60552906261341071769529527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40368604174227381179686351 60552906261341071769529527)
    ·
      refine ⟨90829359392011607654294291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60552906261341071769529527 90829359392011607654294291)
      ·
        refine ⟨136244039088017411481441437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90829359392011607654294291 136244039088017411481441437)
        ·
          refine ⟨51091514658006529305540539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136244039088017411481441437 51091514658006529305540539)
          ·
            refine ⟨76637271987009793958310809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51091514658006529305540539 76637271987009793958310809)
            ·
              refine ⟨57477953990257345468733107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76637271987009793958310809 57477953990257345468733107)
              ·
                refine ⟨86216930985386018203099661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57477953990257345468733107 86216930985386018203099661)
                ·
                  refine ⟨32331349119519756826162373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86216930985386018203099661 32331349119519756826162373)
                  ·
                    refine ⟨6062127959909954404905445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32331349119519756826162373 6062127959909954404905445)
                    ·
                      refine ⟨1136648992483116450919771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6062127959909954404905445 1136648992483116450919771)
                      ·
                        rfl

theorem cell23_2213616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 4].length) (baseStart_2213616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2213616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2213616 prefixEnd_2213616 := by exact prefixLift 2213616
  have htrace : WordTrace (prefixWord ++ tailWord_2213616) baseStart_2213616 baseEnd_2213616 := by
    simpa [prefixWord, tailWord_2213616, baseEnd_2213616] using wordTrace_append hprefix tailTrace_2213616
  have hstable : (prefixWord ++ tailWord_2213616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213616).length < 2 ^ (prefixWord ++ tailWord_2213616).sum := by decide
  have hdescent : baseEnd_2213616 < baseStart_2213616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213638 : List Nat := [6, 2, 2, 1, 2, 1, 1, 8]
def baseStart_2213638 : Nat := 118140960795 + 2213638 * 2 ^ 59
def prefixEnd_2213638 : Nat := 4983230072969 + 3 ^ 40 * 2213638 * 2
def baseEnd_2213638 : Nat := 42098529224352420920173

theorem tailTrace_2213638 : CollatzResearch.WordTrace tailWord_2213638 prefixEnd_2213638 42098529224352420920173 := by
  unfold tailWord_2213638
  simp only [CollatzResearch.WordTrace]
  refine ⟨2523062836074220628646049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 53825340502916706744449045 2523062836074220628646049)
  ·
    refine ⟨1892297127055665471484537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2523062836074220628646049 1892297127055665471484537)
    ·
      refine ⟨1419222845291749103613403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1892297127055665471484537 1419222845291749103613403)
      ·
        refine ⟨2128834267937623655420105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1419222845291749103613403 2128834267937623655420105)
        ·
          refine ⟨1596625700953217741565079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2128834267937623655420105 1596625700953217741565079)
          ·
            refine ⟨2394938551429826612347619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1596625700953217741565079 2394938551429826612347619)
            ·
              refine ⟨3592407827144739918521429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2394938551429826612347619 3592407827144739918521429)
              ·
                refine ⟨42098529224352420920173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3592407827144739918521429 42098529224352420920173)
                ·
                  rfl

theorem cell23_2213638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 8].length) (baseStart_2213638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2213638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2213638 prefixEnd_2213638 := by exact prefixLift 2213638
  have htrace : WordTrace (prefixWord ++ tailWord_2213638) baseStart_2213638 baseEnd_2213638 := by
    simpa [prefixWord, tailWord_2213638, baseEnd_2213638] using wordTrace_append hprefix tailTrace_2213638
  have hstable : (prefixWord ++ tailWord_2213638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213638).length < 2 ^ (prefixWord ++ tailWord_2213638).sum := by decide
  have hdescent : baseEnd_2213638 < baseStart_2213638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213650 : List Nat := [3, 2, 4, 1, 1, 1, 1, 1, 1, 4, 4]
def baseStart_2213650 : Nat := 118140960795 + 2213650 * 2 ^ 59
def prefixEnd_2213650 : Nat := 4983230072969 + 3 ^ 40 * 2213650 * 2
def baseEnd_2213650 : Nat := 1136666450825369317894615

theorem tailTrace_2213650 : CollatzResearch.WordTrace tailWord_2213650 prefixEnd_2213650 1136666450825369317894615 := by
  unfold tailWord_2213650
  simp only [CollatzResearch.WordTrace]
  refine ⟨20184612107582896541527601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53825632286887724110740269 20184612107582896541527601)
  ·
    refine ⟨15138459080687172406145701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20184612107582896541527601 15138459080687172406145701)
    ·
      refine ⟨2838461077628844826152319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15138459080687172406145701 2838461077628844826152319)
      ·
        refine ⟨4257691616443267239228479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2838461077628844826152319 4257691616443267239228479)
        ·
          refine ⟨6386537424664900858842719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4257691616443267239228479 6386537424664900858842719)
          ·
            refine ⟨9579806136997351288264079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6386537424664900858842719 9579806136997351288264079)
            ·
              refine ⟨14369709205496026932396119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9579806136997351288264079 14369709205496026932396119)
              ·
                refine ⟨21554563808244040398594179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14369709205496026932396119 21554563808244040398594179)
                ·
                  refine ⟨32331845712366060597891269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21554563808244040398594179 32331845712366060597891269)
                  ·
                    refine ⟨6062221071068636362104613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32331845712366060597891269 6062221071068636362104613)
                    ·
                      refine ⟨1136666450825369317894615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6062221071068636362104613 1136666450825369317894615)
                      ·
                        rfl

theorem cell23_2213650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_2213650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2213650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2213650 prefixEnd_2213650 := by exact prefixLift 2213650
  have htrace : WordTrace (prefixWord ++ tailWord_2213650) baseStart_2213650 baseEnd_2213650 := by
    simpa [prefixWord, tailWord_2213650, baseEnd_2213650] using wordTrace_append hprefix tailTrace_2213650
  have hstable : (prefixWord ++ tailWord_2213650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213650).length < 2 ^ (prefixWord ++ tailWord_2213650).sum := by decide
  have hdescent : baseEnd_2213650 < baseStart_2213650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213653 : List Nat := [1, 3, 2, 1, 2, 3, 1, 1, 1, 5, 3]
def baseStart_2213653 : Nat := 118140960795 + 2213653 * 2 ^ 59
def prefixEnd_2213653 : Nat := 4983230072969 + 3 ^ 40 * 2213653 * 2
def baseEnd_2213653 : Nat := 1136667991267332806157101

theorem tailTrace_2213653 : CollatzResearch.WordTrace tailWord_2213653 prefixEnd_2213653 1136667991267332806157101 := by
  unfold tailWord_2213653
  simp only [CollatzResearch.WordTrace]
  refine ⟨80738557849320717678469613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53825705232880478452313075 80738557849320717678469613)
  ·
    refine ⟨30276959193495269129426105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80738557849320717678469613 30276959193495269129426105)
    ·
      refine ⟨22707719395121451847069579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30276959193495269129426105 22707719395121451847069579)
      ·
        refine ⟨34061579092682177770604369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22707719395121451847069579 34061579092682177770604369)
        ·
          refine ⟨25546184319511633327953277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34061579092682177770604369 25546184319511633327953277)
          ·
            refine ⟨9579819119816862497982479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25546184319511633327953277 9579819119816862497982479)
            ·
              refine ⟨14369728679725293746973719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9579819119816862497982479 14369728679725293746973719)
              ·
                refine ⟨21554593019587940620460579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14369728679725293746973719 21554593019587940620460579)
                ·
                  refine ⟨32331889529381910930690869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21554593019587940620460579 32331889529381910930690869)
                  ·
                    refine ⟨3031114643379554149752269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32331889529381910930690869 3031114643379554149752269)
                    ·
                      refine ⟨1136667991267332806157101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3031114643379554149752269 1136667991267332806157101)
                      ·
                        rfl

theorem cell23_2213653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 5, 3].length) (baseStart_2213653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2213653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2213653 prefixEnd_2213653 := by exact prefixLift 2213653
  have htrace : WordTrace (prefixWord ++ tailWord_2213653) baseStart_2213653 baseEnd_2213653 := by
    simpa [prefixWord, tailWord_2213653, baseEnd_2213653] using wordTrace_append hprefix tailTrace_2213653
  have hstable : (prefixWord ++ tailWord_2213653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213653).length < 2 ^ (prefixWord ++ tailWord_2213653).sum := by decide
  have hdescent : baseEnd_2213653 < baseStart_2213653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213810 : List Nat := [3, 2, 1, 1, 1, 1, 1, 5, 4, 4]
def baseStart_2213810 : Nat := 118140960795 + 2213810 * 2 ^ 59
def prefixEnd_2213810 : Nat := 4983230072969 + 3 ^ 40 * 2213810 * 2
def baseEnd_2213810 : Nat := 378916202576696230631293

theorem tailTrace_2213810 : CollatzResearch.WordTrace tailWord_2213810 prefixEnd_2213810 378916202576696230631293 := by
  unfold tailWord_2213810
  simp only [CollatzResearch.WordTrace]
  refine ⟨20186071027437983372983721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53829522739834622327956589 20186071027437983372983721)
  ·
    refine ⟨15139553270578487529737791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20186071027437983372983721 15139553270578487529737791)
    ·
      refine ⟨22709329905867731294606687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15139553270578487529737791 22709329905867731294606687)
      ·
        refine ⟨34063994858801596941910031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22709329905867731294606687 34063994858801596941910031)
        ·
          refine ⟨51095992288202395412865047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34063994858801596941910031 51095992288202395412865047)
          ·
            refine ⟨76643988432303593119297571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51095992288202395412865047 76643988432303593119297571)
            ·
              refine ⟨114965982648455389678946357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76643988432303593119297571 114965982648455389678946357)
              ·
                refine ⟨10778060873292692782401221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 114965982648455389678946357 10778060873292692782401221)
                ·
                  refine ⟨2020886413742379896700229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10778060873292692782401221 2020886413742379896700229)
                  ·
                    refine ⟨378916202576696230631293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2020886413742379896700229 378916202576696230631293)
                    ·
                      rfl

theorem cell23_2213810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 4, 4].length) (baseStart_2213810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2213810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2213810 prefixEnd_2213810 := by exact prefixLift 2213810
  have htrace : WordTrace (prefixWord ++ tailWord_2213810) baseStart_2213810 baseEnd_2213810 := by
    simpa [prefixWord, tailWord_2213810, baseEnd_2213810] using wordTrace_append hprefix tailTrace_2213810
  have hstable : (prefixWord ++ tailWord_2213810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213810).length < 2 ^ (prefixWord ++ tailWord_2213810).sum := by decide
  have hdescent : baseEnd_2213810 < baseStart_2213810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213907 : List Nat := [1, 1, 1, 2, 1, 4, 2, 4, 1, 4, 2]
def baseStart_2213907 : Nat := 118140960795 + 2213907 * 2 ^ 59
def prefixEnd_2213907 : Nat := 4983230072969 + 3 ^ 40 * 2213907 * 2
def baseEnd_2213907 : Nat := 1136798415353574812380933

theorem tailTrace_2213907 : CollatzResearch.WordTrace tailWord_2213907 prefixEnd_2213907 1136798415353574812380933 := by
  unfold tailWord_2213907
  simp only [CollatzResearch.WordTrace]
  refine ⟨80747821990400519058215975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53831881326933679372143983 80747821990400519058215975)
  ·
    refine ⟨121121732985600778587323963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80747821990400519058215975 121121732985600778587323963)
    ·
      refine ⟨181682599478401167880985945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121121732985600778587323963 181682599478401167880985945)
      ·
        refine ⟨136261949608800875910739459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181682599478401167880985945 136261949608800875910739459)
        ·
          refine ⟨204392924413201313866109189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136261949608800875910739459 204392924413201313866109189)
          ·
            refine ⟨38323673327475246349895473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 204392924413201313866109189 38323673327475246349895473)
            ·
              refine ⟨28742754995606434762421605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38323673327475246349895473 28742754995606434762421605)
              ·
                refine ⟨5389266561676206517954051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28742754995606434762421605 5389266561676206517954051)
                ·
                  refine ⟨8083899842514309776931077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5389266561676206517954051 8083899842514309776931077)
                  ·
                    refine ⟨1515731220471433083174577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8083899842514309776931077 1515731220471433083174577)
                    ·
                      refine ⟨1136798415353574812380933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1515731220471433083174577 1136798415353574812380933)
                      ·
                        rfl

theorem cell23_2213907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 4, 2].length) (baseStart_2213907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2213907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2213907 prefixEnd_2213907 := by exact prefixLift 2213907
  have htrace : WordTrace (prefixWord ++ tailWord_2213907) baseStart_2213907 baseEnd_2213907 := by
    simpa [prefixWord, tailWord_2213907, baseEnd_2213907] using wordTrace_append hprefix tailTrace_2213907
  have hstable : (prefixWord ++ tailWord_2213907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213907).length < 2 ^ (prefixWord ++ tailWord_2213907).sum := by decide
  have hdescent : baseEnd_2213907 < baseStart_2213907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213981 : List Nat := [1, 4, 4, 1, 1, 2, 1, 4, 5]
def baseStart_2213981 : Nat := 118140960795 + 2213981 * 2 ^ 59
def prefixEnd_2213981 : Nat := 4983230072969 + 3 ^ 40 * 2213981 * 2
def baseEnd_2213981 : Nat := 126315156991334169206177

theorem tailTrace_2213981 : CollatzResearch.WordTrace tailWord_2213981 prefixEnd_2213981 126315156991334169206177 := by
  unfold tailWord_2213981
  simp only [CollatzResearch.WordTrace]
  refine ⟨80750520992132429696409797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53833680661421619797606531 80750520992132429696409797)
  ·
    refine ⟨15140722686024830568076837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80750520992132429696409797 15140722686024830568076837)
    ·
      refine ⟨2838885503629655731514407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15140722686024830568076837 2838885503629655731514407)
      ·
        refine ⟨4258328255444483597271611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2838885503629655731514407 4258328255444483597271611)
        ·
          refine ⟨6387492383166725395907417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4258328255444483597271611 6387492383166725395907417)
          ·
            refine ⟨4790619287375044046930563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6387492383166725395907417 4790619287375044046930563)
            ·
              refine ⟨7185928931062566070395845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4790619287375044046930563 7185928931062566070395845)
              ·
                refine ⟨1347361674574231138199221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7185928931062566070395845 1347361674574231138199221)
                ·
                  refine ⟨126315156991334169206177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1347361674574231138199221 126315156991334169206177)
                  ·
                    rfl

theorem cell23_2213981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 4, 5].length) (baseStart_2213981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2213981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2213981 prefixEnd_2213981 := by exact prefixLift 2213981
  have htrace : WordTrace (prefixWord ++ tailWord_2213981) baseStart_2213981 baseEnd_2213981 := by
    simpa [prefixWord, tailWord_2213981, baseEnd_2213981] using wordTrace_append hprefix tailTrace_2213981
  have hstable : (prefixWord ++ tailWord_2213981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213981).length < 2 ^ (prefixWord ++ tailWord_2213981).sum := by decide
  have hdescent : baseEnd_2213981 < baseStart_2213981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2213997 : List Nat := [1, 5, 1, 1, 2, 1, 2, 2, 1, 3, 4]
def baseStart_2213997 : Nat := 118140960795 + 2213997 * 2 ^ 59
def prefixEnd_2213997 : Nat := 4983230072969 + 3 ^ 40 * 2213997 * 2
def baseEnd_2213997 : Nat := 1136844628612479460255519

theorem tailTrace_2213997 : CollatzResearch.WordTrace tailWord_2213997 prefixEnd_2213997 1136844628612479460255519 := by
  unfold tailWord_2213997
  simp only [CollatzResearch.WordTrace]
  refine ⟨80751104560074464428992245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53834069706716309619328163 80751104560074464428992245)
  ·
    refine ⟨7570416052506981040218023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80751104560074464428992245 7570416052506981040218023)
    ·
      refine ⟨11355624078760471560327035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7570416052506981040218023 11355624078760471560327035)
      ·
        refine ⟨17033436118140707340490553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11355624078760471560327035 17033436118140707340490553)
        ·
          refine ⟨12775077088605530505367915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17033436118140707340490553 12775077088605530505367915)
          ·
            refine ⟨19162615632908295758051873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12775077088605530505367915 19162615632908295758051873)
            ·
              refine ⟨14371961724681221818538905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19162615632908295758051873 14371961724681221818538905)
              ·
                refine ⟨10778971293510916363904179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14371961724681221818538905 10778971293510916363904179)
                ·
                  refine ⟨16168456940266374545856269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10778971293510916363904179 16168456940266374545856269)
                  ·
                    refine ⟨6063171352599890454696101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16168456940266374545856269 6063171352599890454696101)
                    ·
                      refine ⟨1136844628612479460255519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6063171352599890454696101 1136844628612479460255519)
                      ·
                        rfl

theorem cell23_2213997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_2213997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2213997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2213997 prefixEnd_2213997 := by exact prefixLift 2213997
  have htrace : WordTrace (prefixWord ++ tailWord_2213997) baseStart_2213997 baseEnd_2213997 := by
    simpa [prefixWord, tailWord_2213997, baseEnd_2213997] using wordTrace_append hprefix tailTrace_2213997
  have hstable : (prefixWord ++ tailWord_2213997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2213997).length < 2 ^ (prefixWord ++ tailWord_2213997).sum := by decide
  have hdescent : baseEnd_2213997 < baseStart_2213997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2213997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214007 : List Nat := [1, 1, 3, 1, 1, 5, 1, 1, 5, 4]
def baseStart_2214007 : Nat := 118140960795 + 2214007 * 2 ^ 59
def prefixEnd_2214007 : Nat := 4983230072969 + 3 ^ 40 * 2214007 * 2
def baseEnd_2214007 : Nat := 378949921139674807043491

theorem tailTrace_2214007 : CollatzResearch.WordTrace tailWord_2214007 prefixEnd_2214007 378949921139674807043491 := by
  unfold tailWord_2214007
  simp only [CollatzResearch.WordTrace]
  refine ⟨80751469290038236136856275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53834312860025490757904183 80751469290038236136856275)
  ·
    refine ⟨121127203935057354205284413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80751469290038236136856275 121127203935057354205284413)
    ·
      refine ⟨45422701475646507826981655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121127203935057354205284413 45422701475646507826981655)
      ·
        refine ⟨68134052213469761740472483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45422701475646507826981655 68134052213469761740472483)
        ·
          refine ⟨102201078320204642610708725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68134052213469761740472483 102201078320204642610708725)
          ·
            refine ⟨9581351092519185244753943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 102201078320204642610708725 9581351092519185244753943)
            ·
              refine ⟨14372026638778777867130915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9581351092519185244753943 14372026638778777867130915)
              ·
                refine ⟨21558039958168166800696373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14372026638778777867130915 21558039958168166800696373)
                ·
                  refine ⟨2021066246078265637565285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21558039958168166800696373 2021066246078265637565285)
                  ·
                    refine ⟨378949921139674807043491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2021066246078265637565285 378949921139674807043491)
                    ·
                      rfl

theorem cell23_2214007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 5, 4].length) (baseStart_2214007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2214007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2214007 prefixEnd_2214007 := by exact prefixLift 2214007
  have htrace : WordTrace (prefixWord ++ tailWord_2214007) baseStart_2214007 baseEnd_2214007 := by
    simpa [prefixWord, tailWord_2214007, baseEnd_2214007] using wordTrace_append hprefix tailTrace_2214007
  have hstable : (prefixWord ++ tailWord_2214007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214007).length < 2 ^ (prefixWord ++ tailWord_2214007).sum := by decide
  have hdescent : baseEnd_2214007 < baseStart_2214007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214010 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 6, 1, 6]
def baseStart_2214010 : Nat := 118140960795 + 2214010 * 2 ^ 59
def prefixEnd_2214010 : Nat := 4983230072969 + 3 ^ 40 * 2214010 * 2
def baseEnd_2214010 : Nat := 1136851303860987909392959

theorem tailTrace_2214010 : CollatzResearch.WordTrace tailWord_2214010 prefixEnd_2214010 1136851303860987909392959 := by
  unfold tailWord_2214010
  simp only [CollatzResearch.WordTrace]
  refine ⟨20187894677256841912303871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53834385806018245099476989 20187894677256841912303871)
  ·
    refine ⟨30281842015885262868455807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20187894677256841912303871 30281842015885262868455807)
    ·
      refine ⟨45422763023827894302683711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30281842015885262868455807 45422763023827894302683711)
      ·
        refine ⟨68134144535741841454025567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45422763023827894302683711 68134144535741841454025567)
        ·
          refine ⟨102201216803612762181038351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68134144535741841454025567 102201216803612762181038351)
          ·
            refine ⟨153301825205419143271557527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102201216803612762181038351 153301825205419143271557527)
            ·
              refine ⟨229952737808128714907336291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153301825205419143271557527 229952737808128714907336291)
              ·
                refine ⟨344929106712193072361004437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 229952737808128714907336291 344929106712193072361004437)
                ·
                  refine ⟨16168551877134050266922083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 344929106712193072361004437 16168551877134050266922083)
                  ·
                    refine ⟨24252827815701075400383125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16168551877134050266922083 24252827815701075400383125)
                    ·
                      refine ⟨1136851303860987909392959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24252827815701075400383125 1136851303860987909392959)
                      ·
                        rfl

theorem cell23_2214010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 6, 1, 6].length) (baseStart_2214010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2214010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2214010 prefixEnd_2214010 := by exact prefixLift 2214010
  have htrace : WordTrace (prefixWord ++ tailWord_2214010) baseStart_2214010 baseEnd_2214010 := by
    simpa [prefixWord, tailWord_2214010, baseEnd_2214010] using wordTrace_append hprefix tailTrace_2214010
  have hstable : (prefixWord ++ tailWord_2214010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214010).length < 2 ^ (prefixWord ++ tailWord_2214010).sum := by decide
  have hdescent : baseEnd_2214010 < baseStart_2214010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214034 : List Nat := [3, 2, 3, 1, 1, 1, 2, 1, 4, 2, 3]
def baseStart_2214034 : Nat := 118140960795 + 2214034 * 2 ^ 59
def prefixEnd_2214034 : Nat := 4983230072969 + 3 ^ 40 * 2214034 * 2
def baseEnd_2214034 : Nat := 1136863627396695815492849

theorem tailTrace_2214034 : CollatzResearch.WordTrace tailWord_2214034 prefixEnd_2214034 1136863627396695815492849 := by
  unfold tailWord_2214034
  simp only [CollatzResearch.WordTrace]
  refine ⟨20188113515235104937022289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53834969373960279832059437 20188113515235104937022289)
  ·
    refine ⟨15141085136426328702766717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20188113515235104937022289 15141085136426328702766717)
    ·
      refine ⟨5677906926159873263537519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15141085136426328702766717 5677906926159873263537519)
      ·
        refine ⟨8516860389239809895306279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5677906926159873263537519 8516860389239809895306279)
        ·
          refine ⟨12775290583859714842959419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8516860389239809895306279 12775290583859714842959419)
          ·
            refine ⟨19162935875789572264439129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12775290583859714842959419 19162935875789572264439129)
            ·
              refine ⟨14372201906842179198329347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19162935875789572264439129 14372201906842179198329347)
              ·
                refine ⟨21558302860263268797494021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14372201906842179198329347 21558302860263268797494021)
                ·
                  refine ⟨4042181786299362899530129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21558302860263268797494021 4042181786299362899530129)
                  ·
                    refine ⟨3031636339724522174647597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4042181786299362899530129 3031636339724522174647597)
                    ·
                      refine ⟨1136863627396695815492849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3031636339724522174647597 1136863627396695815492849)
                      ·
                        rfl

theorem cell23_2214034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_2214034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2214034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2214034 prefixEnd_2214034 := by exact prefixLift 2214034
  have htrace : WordTrace (prefixWord ++ tailWord_2214034) baseStart_2214034 baseEnd_2214034 := by
    simpa [prefixWord, tailWord_2214034, baseEnd_2214034] using wordTrace_append hprefix tailTrace_2214034
  have hstable : (prefixWord ++ tailWord_2214034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214034).length < 2 ^ (prefixWord ++ tailWord_2214034).sum := by decide
  have hdescent : baseEnd_2214034 < baseStart_2214034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214074 : List Nat := [3, 1, 1, 1, 2, 2, 4, 1, 1, 5, 2]
def baseStart_2214074 : Nat := 118140960795 + 2214074 * 2 ^ 59
def prefixEnd_2214074 : Nat := 4983230072969 + 3 ^ 40 * 2214074 * 2
def baseEnd_2214074 : Nat := 1136884166622875658992665

theorem tailTrace_2214074 : CollatzResearch.WordTrace tailWord_2214074 prefixEnd_2214074 1136884166622875658992665 := by
  unfold tailWord_2214074
  simp only [CollatzResearch.WordTrace]
  refine ⟨20188478245198876644886319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53835941987197004386363517 20188478245198876644886319)
  ·
    refine ⟨30282717367798314967329479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20188478245198876644886319 30282717367798314967329479)
    ·
      refine ⟨45424076051697472450994219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30282717367798314967329479 45424076051697472450994219)
      ·
        refine ⟨68136114077546208676491329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45424076051697472450994219 68136114077546208676491329)
        ·
          refine ⟨51102085558159656507368497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68136114077546208676491329 51102085558159656507368497)
          ·
            refine ⟨38326564168619742380526373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51102085558159656507368497 38326564168619742380526373)
            ·
              refine ⟨7186230781616201696348695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38326564168619742380526373 7186230781616201696348695)
              ·
                refine ⟨10779346172424302544523043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7186230781616201696348695 10779346172424302544523043)
                ·
                  refine ⟨16169019258636453816784565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10779346172424302544523043 16169019258636453816784565)
                  ·
                    refine ⟨1515845555497167545323553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16169019258636453816784565 1515845555497167545323553)
                    ·
                      refine ⟨1136884166622875658992665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1515845555497167545323553 1136884166622875658992665)
                      ·
                        rfl

theorem cell23_2214074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 1, 5, 2].length) (baseStart_2214074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2214074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2214074 prefixEnd_2214074 := by exact prefixLift 2214074
  have htrace : WordTrace (prefixWord ++ tailWord_2214074) baseStart_2214074 baseEnd_2214074 := by
    simpa [prefixWord, tailWord_2214074, baseEnd_2214074] using wordTrace_append hprefix tailTrace_2214074
  have hstable : (prefixWord ++ tailWord_2214074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214074).length < 2 ^ (prefixWord ++ tailWord_2214074).sum := by decide
  have hdescent : baseEnd_2214074 < baseStart_2214074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214087 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 7, 1, 4]
def baseStart_2214087 : Nat := 118140960795 + 2214087 * 2 ^ 59
def prefixEnd_2214087 : Nat := 4983230072969 + 3 ^ 40 * 2214087 * 2
def baseEnd_2214087 : Nat := 1136890841871384108130105

theorem tailTrace_2214087 : CollatzResearch.WordTrace tailWord_2214087 prefixEnd_2214087 1136890841871384108130105 := by
  unfold tailWord_2214087
  simp only [CollatzResearch.WordTrace]
  refine ⟨80754387129748409799768515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53836258086498939866512343 80754387129748409799768515)
  ·
    refine ⟨121131580694622614699652773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80754387129748409799768515 121131580694622614699652773)
    ·
      refine ⟨22712171380241740256184895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121131580694622614699652773 22712171380241740256184895)
      ·
        refine ⟨34068257070362610384277343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22712171380241740256184895 34068257070362610384277343)
        ·
          refine ⟨51102385605543915576416015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34068257070362610384277343 51102385605543915576416015)
          ·
            refine ⟨76653578408315873364624023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51102385605543915576416015 76653578408315873364624023)
            ·
              refine ⟨114980367612473810046936035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76653578408315873364624023 114980367612473810046936035)
              ·
                refine ⟨172470551418710715070404053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114980367612473810046936035 172470551418710715070404053)
                ·
                  refine ⟨4042278548876032384462595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 172470551418710715070404053 4042278548876032384462595)
                  ·
                    refine ⟨6063417823314048576693893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4042278548876032384462595 6063417823314048576693893)
                    ·
                      refine ⟨1136890841871384108130105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6063417823314048576693893 1136890841871384108130105)
                      ·
                        rfl

theorem cell23_2214087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_2214087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2214087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2214087 prefixEnd_2214087 := by exact prefixLift 2214087
  have htrace : WordTrace (prefixWord ++ tailWord_2214087) baseStart_2214087 baseEnd_2214087 := by
    simpa [prefixWord, tailWord_2214087, baseEnd_2214087] using wordTrace_append hprefix tailTrace_2214087
  have hstable : (prefixWord ++ tailWord_2214087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214087).length < 2 ^ (prefixWord ++ tailWord_2214087).sum := by decide
  have hdescent : baseEnd_2214087 < baseStart_2214087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214098 : List Nat := [3, 2, 2, 2, 1, 4, 1, 1, 3, 1, 3]
def baseStart_2214098 : Nat := 118140960795 + 2214098 * 2 ^ 59
def prefixEnd_2214098 : Nat := 4983230072969 + 3 ^ 40 * 2214098 * 2
def baseEnd_2214098 : Nat := 1136896490158583565092555

theorem tailTrace_2214098 : CollatzResearch.WordTrace tailWord_2214098 prefixEnd_2214098 1136896490158583565092555 := by
  unfold tailWord_2214098
  simp only [CollatzResearch.WordTrace]
  refine ⟨20188697083177139669604737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53836525555139039118945965 20188697083177139669604737)
  ·
    refine ⟨15141522812382854752203553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20188697083177139669604737 15141522812382854752203553)
    ·
      refine ⟨11356142109287141064152665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15141522812382854752203553 11356142109287141064152665)
      ·
        refine ⟨8517106581965355798114499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11356142109287141064152665 8517106581965355798114499)
        ·
          refine ⟨12775659872948033697171749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8517106581965355798114499 12775659872948033697171749)
          ·
            refine ⟨2395436226177756318219703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12775659872948033697171749 2395436226177756318219703)
            ·
              refine ⟨3593154339266634477329555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2395436226177756318219703 3593154339266634477329555)
              ·
                refine ⟨5389731508899951715994333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3593154339266634477329555 5389731508899951715994333)
                ·
                  refine ⟨2021149315837481893497875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5389731508899951715994333 2021149315837481893497875)
                  ·
                    refine ⟨3031723973756222840246813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2021149315837481893497875 3031723973756222840246813)
                    ·
                      refine ⟨1136896490158583565092555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3031723973756222840246813 1136896490158583565092555)
                      ·
                        rfl

theorem cell23_2214098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_2214098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2214098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2214098 prefixEnd_2214098 := by exact prefixLift 2214098
  have htrace : WordTrace (prefixWord ++ tailWord_2214098) baseStart_2214098 baseEnd_2214098 := by
    simpa [prefixWord, tailWord_2214098, baseEnd_2214098] using wordTrace_append hprefix tailTrace_2214098
  have hstable : (prefixWord ++ tailWord_2214098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214098).length < 2 ^ (prefixWord ++ tailWord_2214098).sum := by decide
  have hdescent : baseEnd_2214098 < baseStart_2214098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214124 : List Nat := [2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 3]
def baseStart_2214124 : Nat := 118140960795 + 2214124 * 2 ^ 59
def prefixEnd_2214124 : Nat := 4983230072969 + 3 ^ 40 * 2214124 * 2
def baseEnd_2214124 : Nat := 1136909840655600463367435

theorem tailTrace_2214124 : CollatzResearch.WordTrace tailWord_2214124 prefixEnd_2214124 1136909840655600463367435 := by
  unfold tailWord_2214124
  simp only [CollatzResearch.WordTrace]
  refine ⟨40377868315307182559432713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53837157753742910079243617 40377868315307182559432713)
  ·
    refine ⟨30283401236480386919574535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40377868315307182559432713 30283401236480386919574535)
    ·
      refine ⟨45425101854720580379361803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30283401236480386919574535 45425101854720580379361803)
      ·
        refine ⟨68137652782080870569042705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45425101854720580379361803 68137652782080870569042705)
        ·
          refine ⟨51103239586560652926782029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68137652782080870569042705 51103239586560652926782029)
          ·
            refine ⟨19163714844960244847543261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51103239586560652926782029 19163714844960244847543261)
            ·
              refine ⟨7186393066860091817828723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19163714844960244847543261 7186393066860091817828723)
              ·
                refine ⟨10779589600290137726743085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7186393066860091817828723 10779589600290137726743085)
                ·
                  refine ⟨4042346100108801647528657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10779589600290137726743085 4042346100108801647528657)
                  ·
                    refine ⟨3031759575081601235646493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4042346100108801647528657 3031759575081601235646493)
                    ·
                      refine ⟨1136909840655600463367435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3031759575081601235646493 1136909840655600463367435)
                      ·
                        rfl

theorem cell23_2214124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 3].length) (baseStart_2214124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2214124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2214124 prefixEnd_2214124 := by exact prefixLift 2214124
  have htrace : WordTrace (prefixWord ++ tailWord_2214124) baseStart_2214124 baseEnd_2214124 := by
    simpa [prefixWord, tailWord_2214124, baseEnd_2214124] using wordTrace_append hprefix tailTrace_2214124
  have hstable : (prefixWord ++ tailWord_2214124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214124).length < 2 ^ (prefixWord ++ tailWord_2214124).sum := by decide
  have hdescent : baseEnd_2214124 < baseStart_2214124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214127 : List Nat := [1, 1, 2, 1, 6, 1, 2, 9]
def baseStart_2214127 : Nat := 118140960795 + 2214127 * 2 ^ 59
def prefixEnd_2214127 : Nat := 4983230072969 + 3 ^ 40 * 2214127 * 2
def baseEnd_2214127 : Nat := 42107828929539405615923

theorem tailTrace_2214127 : CollatzResearch.WordTrace tailWord_2214127 prefixEnd_2214127 42107828929539405615923 := by
  unfold tailWord_2214127
  simp only [CollatzResearch.WordTrace]
  refine ⟨80755846049603496631224635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53837230699735664420816423 80755846049603496631224635)
  ·
    refine ⟨121133769074405244946836953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80755846049603496631224635 121133769074405244946836953)
    ·
      refine ⟨90850326805803933710127715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121133769074405244946836953 90850326805803933710127715)
      ·
        refine ⟨136275490208705900565191573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90850326805803933710127715 136275490208705900565191573)
        ·
          refine ⟨6387913603533089088993355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 136275490208705900565191573 6387913603533089088993355)
          ·
            refine ⟨9581870405299633633490033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6387913603533089088993355 9581870405299633633490033)
            ·
              refine ⟨7186402803974725225117525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9581870405299633633490033 7186402803974725225117525)
              ·
                refine ⟨42107828929539405615923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7186402803974725225117525 42107828929539405615923)
                ·
                  rfl

theorem cell23_2214127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 9].length) (baseStart_2214127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2214127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2214127 prefixEnd_2214127 := by exact prefixLift 2214127
  have htrace : WordTrace (prefixWord ++ tailWord_2214127) baseStart_2214127 baseEnd_2214127 := by
    simpa [prefixWord, tailWord_2214127, baseEnd_2214127] using wordTrace_append hprefix tailTrace_2214127
  have hstable : (prefixWord ++ tailWord_2214127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214127).length < 2 ^ (prefixWord ++ tailWord_2214127).sum := by decide
  have hdescent : baseEnd_2214127 < baseStart_2214127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214134 : List Nat := [5, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4]
def baseStart_2214134 : Nat := 118140960795 + 2214134 * 2 ^ 59
def prefixEnd_2214134 : Nat := 4983230072969 + 3 ^ 40 * 2214134 * 2
def baseEnd_2214134 : Nat := 1136914975462145424242389

theorem tailTrace_2214134 : CollatzResearch.WordTrace tailWord_2214134 prefixEnd_2214134 1136914975462145424242389 := by
  unfold tailWord_2214134
  simp only [CollatzResearch.WordTrace]
  refine ⟨5047256335036133551670591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53837400907052091217819637 5047256335036133551670591)
  ·
    refine ⟨7570884502554200327505887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5047256335036133551670591 7570884502554200327505887)
    ·
      refine ⟨11356326753831300491258831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7570884502554200327505887 11356326753831300491258831)
      ·
        refine ⟨17034490130746950736888247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11356326753831300491258831 17034490130746950736888247)
        ·
          refine ⟨25551735196120426105332371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17034490130746950736888247 25551735196120426105332371)
          ·
            refine ⟨38327602794180639157998557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25551735196120426105332371 38327602794180639157998557)
            ·
              refine ⟨14372851047817739684249459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38327602794180639157998557 14372851047817739684249459)
              ·
                refine ⟨21559276571726609526374189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14372851047817739684249459 21559276571726609526374189)
                ·
                  refine ⟨8084728714397478572390321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21559276571726609526374189 8084728714397478572390321)
                  ·
                    refine ⟨6063546535798108929292741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8084728714397478572390321 6063546535798108929292741)
                    ·
                      refine ⟨1136914975462145424242389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6063546535798108929292741 1136914975462145424242389)
                      ·
                        rfl

theorem cell23_2214134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_2214134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2214134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2214134 prefixEnd_2214134 := by exact prefixLift 2214134
  have htrace : WordTrace (prefixWord ++ tailWord_2214134) baseStart_2214134 baseEnd_2214134 := by
    simpa [prefixWord, tailWord_2214134, baseEnd_2214134] using wordTrace_append hprefix tailTrace_2214134
  have hstable : (prefixWord ++ tailWord_2214134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214134).length < 2 ^ (prefixWord ++ tailWord_2214134).sum := by decide
  have hdescent : baseEnd_2214134 < baseStart_2214134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214148 : List Nat := [2, 3, 2, 2, 3, 1, 2, 2, 2, 4]
def baseStart_2214148 : Nat := 118140960795 + 2214148 * 2 ^ 59
def prefixEnd_2214148 : Nat := 4983230072969 + 3 ^ 40 * 2214148 * 2
def baseEnd_2214148 : Nat := 378974054730436123155775

theorem tailTrace_2214148 : CollatzResearch.WordTrace tailWord_2214148 prefixEnd_2214148 378974054730436123155775 := by
  unfold tailWord_2214148
  simp only [CollatzResearch.WordTrace]
  refine ⟨40378305991263708608869549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53837741321684944811826065 40378305991263708608869549)
  ·
    refine ⟨15141864746723890728326081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40378305991263708608869549 15141864746723890728326081)
    ·
      refine ⟨11356398560042918046244561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15141864746723890728326081 11356398560042918046244561)
      ·
        refine ⟨8517298920032188534683421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11356398560042918046244561 8517298920032188534683421)
        ·
          refine ⟨3193987095012070700506283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8517298920032188534683421 3193987095012070700506283)
          ·
            refine ⟨4790980642518106050759425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3193987095012070700506283 4790980642518106050759425)
            ·
              refine ⟨3593235481888579538069569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4790980642518106050759425 3593235481888579538069569)
              ·
                refine ⟨2694926611416434653552177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3593235481888579538069569 2694926611416434653552177)
                ·
                  refine ⟨2021194958562325990164133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2694926611416434653552177 2021194958562325990164133)
                  ·
                    refine ⟨378974054730436123155775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2021194958562325990164133 378974054730436123155775)
                    ·
                      rfl

theorem cell23_2214148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_2214148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2214148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2214148 prefixEnd_2214148 := by exact prefixLift 2214148
  have htrace : WordTrace (prefixWord ++ tailWord_2214148) baseStart_2214148 baseEnd_2214148 := by
    simpa [prefixWord, tailWord_2214148, baseEnd_2214148] using wordTrace_append hprefix tailTrace_2214148
  have hstable : (prefixWord ++ tailWord_2214148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214148).length < 2 ^ (prefixWord ++ tailWord_2214148).sum := by decide
  have hdescent : baseEnd_2214148 < baseStart_2214148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214171 : List Nat := [1, 1, 1, 1, 1, 1, 8, 3, 2, 1, 3]
def baseStart_2214171 : Nat := 118140960795 + 2214171 * 2 ^ 59
def prefixEnd_2214171 : Nat := 4983230072969 + 3 ^ 40 * 2214171 * 2
def baseEnd_2214171 : Nat := 1136933974246361779479719

theorem tailTrace_2214171 : CollatzResearch.WordTrace tailWord_2214171 prefixEnd_2214171 1136933974246361779479719 := by
  unfold tailWord_2214171
  simp only [CollatzResearch.WordTrace]
  refine ⟨80757450861444092145826367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53838300574296061430550911 80757450861444092145826367)
  ·
    refine ⟨121136176292166138218739551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80757450861444092145826367 121136176292166138218739551)
    ·
      refine ⟨181704264438249207328109327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121136176292166138218739551 181704264438249207328109327)
      ·
        refine ⟨272556396657373810992163991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181704264438249207328109327 272556396657373810992163991)
        ·
          refine ⟨408834594986060716488245987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272556396657373810992163991 408834594986060716488245987)
          ·
            refine ⟨613251892479091074732368981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408834594986060716488245987 613251892479091074732368981)
            ·
              refine ⟨7186545614989348532019949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 613251892479091074732368981 7186545614989348532019949)
              ·
                refine ⟨2694954605621005699507481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7186545614989348532019949 2694954605621005699507481)
                ·
                  refine ⟨2021215954215754274630611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2694954605621005699507481 2021215954215754274630611)
                  ·
                    refine ⟨3031823931323631411945917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2021215954215754274630611 3031823931323631411945917)
                    ·
                      refine ⟨1136933974246361779479719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3031823931323631411945917 1136933974246361779479719)
                      ·
                        rfl

theorem cell23_2214171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 3, 2, 1, 3].length) (baseStart_2214171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2214171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2214171 prefixEnd_2214171 := by exact prefixLift 2214171
  have htrace : WordTrace (prefixWord ++ tailWord_2214171) baseStart_2214171 baseEnd_2214171 := by
    simpa [prefixWord, tailWord_2214171, baseEnd_2214171] using wordTrace_append hprefix tailTrace_2214171
  have hstable : (prefixWord ++ tailWord_2214171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214171).length < 2 ^ (prefixWord ++ tailWord_2214171).sum := by decide
  have hdescent : baseEnd_2214171 < baseStart_2214171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214189 : List Nat := [1, 5, 3, 1, 2, 1, 2, 3, 1, 2, 2]
def baseStart_2214189 : Nat := 118140960795 + 2214189 * 2 ^ 59
def prefixEnd_2214189 : Nat := 4983230072969 + 3 ^ 40 * 2214189 * 2
def baseEnd_2214189 : Nat := 1136943216898142709054637

theorem tailTrace_2214189 : CollatzResearch.WordTrace tailWord_2214189 prefixEnd_2214189 1136943216898142709054637 := by
  unfold tailWord_2214189
  simp only [CollatzResearch.WordTrace]
  refine ⟨80758107375378881219981621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53838738250252587479987747 80758107375378881219981621)
  ·
    refine ⟨7571072566441770114373277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80758107375378881219981621 7571072566441770114373277)
    ·
      refine ⟨2839152212415663792889979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7571072566441770114373277 2839152212415663792889979)
      ·
        refine ⟨4258728318623495689334969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2839152212415663792889979 4258728318623495689334969)
        ·
          refine ⟨3194046238967621767001227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4258728318623495689334969 3194046238967621767001227)
          ·
            refine ⟨4791069358451432650501841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3194046238967621767001227 4791069358451432650501841)
            ·
              refine ⟨3593302018838574487876381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4791069358451432650501841 3593302018838574487876381)
              ·
                refine ⟨1347488257064465432953643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3593302018838574487876381 1347488257064465432953643)
                ·
                  refine ⟨2021232385596698149430465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1347488257064465432953643 2021232385596698149430465)
                  ·
                    refine ⟨1515924289197523612072849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2021232385596698149430465 1515924289197523612072849)
                    ·
                      refine ⟨1136943216898142709054637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1515924289197523612072849 1136943216898142709054637)
                      ·
                        rfl

theorem cell23_2214189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_2214189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2214189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2214189 prefixEnd_2214189 := by exact prefixLift 2214189
  have htrace : WordTrace (prefixWord ++ tailWord_2214189) baseStart_2214189 baseEnd_2214189 := by
    simpa [prefixWord, tailWord_2214189, baseEnd_2214189] using wordTrace_append hprefix tailTrace_2214189
  have hstable : (prefixWord ++ tailWord_2214189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214189).length < 2 ^ (prefixWord ++ tailWord_2214189).sum := by decide
  have hdescent : baseEnd_2214189 < baseStart_2214189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214224 : List Nat := [2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 4]
def baseStart_2214224 : Nat := 118140960795 + 2214224 * 2 ^ 59
def prefixEnd_2214224 : Nat := 4983230072969 + 3 ^ 40 * 2214224 * 2
def baseEnd_2214224 : Nat := 1136961188721050072116975

theorem tailTrace_2214224 : CollatzResearch.WordTrace tailWord_2214224 prefixEnd_2214224 1136961188721050072116975 := by
  unfold tailWord_2214224
  simp only [CollatzResearch.WordTrace]
  refine ⟨40379691965126041098752863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53839589286834721465003817 40379691965126041098752863)
  ·
    refine ⟨60569537947689061648129295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40379691965126041098752863 60569537947689061648129295)
    ·
      refine ⟨90854306921533592472193943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60569537947689061648129295 90854306921533592472193943)
      ·
        refine ⟨136281460382300388708290915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90854306921533592472193943 136281460382300388708290915)
        ·
          refine ⟨204422190573450583062436373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136281460382300388708290915 204422190573450583062436373)
          ·
            refine ⟨9582290183130496081051705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 204422190573450583062436373 9582290183130496081051705)
            ·
              refine ⟨7186717637347872060788779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9582290183130496081051705 7186717637347872060788779)
              ·
                refine ⟨10780076456021808091183169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7186717637347872060788779 10780076456021808091183169)
                ·
                  refine ⟨8085057342016356068387377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10780076456021808091183169 8085057342016356068387377)
                  ·
                    refine ⟨6063793006512267051290533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8085057342016356068387377 6063793006512267051290533)
                    ·
                      refine ⟨1136961188721050072116975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6063793006512267051290533 1136961188721050072116975)
                      ·
                        rfl

theorem cell23_2214224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 4].length) (baseStart_2214224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2214224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2214224 prefixEnd_2214224 := by exact prefixLift 2214224
  have htrace : WordTrace (prefixWord ++ tailWord_2214224) baseStart_2214224 baseEnd_2214224 := by
    simpa [prefixWord, tailWord_2214224, baseEnd_2214224] using wordTrace_append hprefix tailTrace_2214224
  have hstable : (prefixWord ++ tailWord_2214224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214224).length < 2 ^ (prefixWord ++ tailWord_2214224).sum := by decide
  have hdescent : baseEnd_2214224 < baseStart_2214224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214228 : List Nat := [2, 4, 1, 1, 2, 2, 3, 1, 1, 4, 2]
def baseStart_2214228 : Nat := 118140960795 + 2214228 * 2 ^ 59
def prefixEnd_2214228 : Nat := 4983230072969 + 3 ^ 40 * 2214228 * 2
def baseEnd_2214228 : Nat := 1136963242643668056466957

theorem tailTrace_2214228 : CollatzResearch.WordTrace tailWord_2214228 prefixEnd_2214228 1136963242643668056466957 := by
  unfold tailWord_2214228
  simp only [CollatzResearch.WordTrace]
  refine ⟨40379764911118795440325669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53839686548158393920434225 40379764911118795440325669)
  ·
    refine ⟨7571205920834774145061063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40379764911118795440325669 7571205920834774145061063)
    ·
      refine ⟨11356808881252161217591595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7571205920834774145061063 11356808881252161217591595)
      ·
        refine ⟨17035213321878241826387393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11356808881252161217591595 17035213321878241826387393)
        ·
          refine ⟨12776409991408681369790545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17035213321878241826387393 12776409991408681369790545)
          ·
            refine ⟨9582307493556511027342909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12776409991408681369790545 9582307493556511027342909)
            ·
              refine ⟨3593365310083691635253591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9582307493556511027342909 3593365310083691635253591)
              ·
                refine ⟨5390047965125537452880387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3593365310083691635253591 5390047965125537452880387)
                ·
                  refine ⟨8085071947688306179320581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5390047965125537452880387 8085071947688306179320581)
                  ·
                    refine ⟨1515950990191557408622609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8085071947688306179320581 1515950990191557408622609)
                    ·
                      refine ⟨1136963242643668056466957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1515950990191557408622609 1136963242643668056466957)
                      ·
                        rfl

theorem cell23_2214228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 1, 4, 2].length) (baseStart_2214228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2214228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2214228 prefixEnd_2214228 := by exact prefixLift 2214228
  have htrace : WordTrace (prefixWord ++ tailWord_2214228) baseStart_2214228 baseEnd_2214228 := by
    simpa [prefixWord, tailWord_2214228, baseEnd_2214228] using wordTrace_append hprefix tailTrace_2214228
  have hstable : (prefixWord ++ tailWord_2214228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214228).length < 2 ^ (prefixWord ++ tailWord_2214228).sum := by decide
  have hdescent : baseEnd_2214228 < baseStart_2214228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214385 : List Nat := [1, 2, 2, 2, 3, 1, 1, 6, 1, 1, 3]
def baseStart_2214385 : Nat := 118140960795 + 2214385 * 2 ^ 59
def prefixEnd_2214385 : Nat := 4983230072969 + 3 ^ 40 * 2214385 * 2
def baseEnd_2214385 : Nat := 1137043859106423942203735

theorem tailTrace_2214385 : CollatzResearch.WordTrace tailWord_2214385 prefixEnd_2214385 1137043859106423942203735 := by
  unfold tailWord_2214385
  simp only [CollatzResearch.WordTrace]
  refine ⟨80765256082668806694116609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53843504055112537796077739 80765256082668806694116609)
  ·
    refine ⟨60573942062001605020587457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80765256082668806694116609 60573942062001605020587457)
    ·
      refine ⟨45430456546501203765440593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60573942062001605020587457 45430456546501203765440593)
      ·
        refine ⟨34072842409875902824080445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45430456546501203765440593 34072842409875902824080445)
        ·
          refine ⟨12777315903703463559030167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34072842409875902824080445 12777315903703463559030167)
          ·
            refine ⟨19165973855555195338545251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12777315903703463559030167 19165973855555195338545251)
            ·
              refine ⟨28748960783332793007817877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19165973855555195338545251 28748960783332793007817877)
              ·
                refine ⟨1347607536718724672241463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28748960783332793007817877 1347607536718724672241463)
                ·
                  refine ⟨2021411305078087008362195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1347607536718724672241463 2021411305078087008362195)
                  ·
                    refine ⟨3032116957617130512543293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2021411305078087008362195 3032116957617130512543293)
                    ·
                      refine ⟨1137043859106423942203735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3032116957617130512543293 1137043859106423942203735)
                      ·
                        rfl

theorem cell23_2214385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 6, 1, 1, 3].length) (baseStart_2214385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2214385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2214385 prefixEnd_2214385 := by exact prefixLift 2214385
  have htrace : WordTrace (prefixWord ++ tailWord_2214385) baseStart_2214385 baseEnd_2214385 := by
    simpa [prefixWord, tailWord_2214385, baseEnd_2214385] using wordTrace_append hprefix tailTrace_2214385
  have hstable : (prefixWord ++ tailWord_2214385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214385).length < 2 ^ (prefixWord ++ tailWord_2214385).sum := by decide
  have hdescent : baseEnd_2214385 < baseStart_2214385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214421 : List Nat := [1, 3, 2, 1, 3, 1, 2, 1, 3, 2, 4]
def baseStart_2214421 : Nat := 118140960795 + 2214421 * 2 ^ 59
def prefixEnd_2214421 : Nat := 4983230072969 + 3 ^ 40 * 2214421 * 2
def baseEnd_2214421 : Nat := 1137062344409985801353569

theorem tailTrace_2214421 : CollatzResearch.WordTrace tailWord_2214421 prefixEnd_2214421 1137062344409985801353569 := by
  unfold tailWord_2214421
  simp only [CollatzResearch.WordTrace]
  refine ⟨80766569110538384842427117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53844379407025589894951411 80766569110538384842427117)
  ·
    refine ⟨30287463416451894315910169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80766569110538384842427117 30287463416451894315910169)
    ·
      refine ⟨22715597562338920736932627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30287463416451894315910169 22715597562338920736932627)
      ·
        refine ⟨34073396343508381105398941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22715597562338920736932627 34073396343508381105398941)
        ·
          refine ⟨12777523628815642914524603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34073396343508381105398941 12777523628815642914524603)
          ·
            refine ⟨19166285443223464371786905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12777523628815642914524603 19166285443223464371786905)
            ·
              refine ⟨14374714082417598278840179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19166285443223464371786905 14374714082417598278840179)
              ·
                refine ⟨21562071123626397418260269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14374714082417598278840179 21562071123626397418260269)
                ·
                  refine ⟨8085776671359899031847601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21562071123626397418260269 8085776671359899031847601)
                  ·
                    refine ⟨6064332503519924273885701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8085776671359899031847601 6064332503519924273885701)
                    ·
                      refine ⟨1137062344409985801353569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6064332503519924273885701 1137062344409985801353569)
                      ·
                        rfl

theorem cell23_2214421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_2214421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2214421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2214421 prefixEnd_2214421 := by exact prefixLift 2214421
  have htrace : WordTrace (prefixWord ++ tailWord_2214421) baseStart_2214421 baseEnd_2214421 := by
    simpa [prefixWord, tailWord_2214421, baseEnd_2214421] using wordTrace_append hprefix tailTrace_2214421
  have hstable : (prefixWord ++ tailWord_2214421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214421).length < 2 ^ (prefixWord ++ tailWord_2214421).sum := by decide
  have hdescent : baseEnd_2214421 < baseStart_2214421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214428 : List Nat := [2, 2, 3, 1, 2, 3, 2, 1, 1, 1, 5]
def baseStart_2214428 : Nat := 118140960795 + 2214428 * 2 ^ 59
def prefixEnd_2214428 : Nat := 4983230072969 + 3 ^ 40 * 2214428 * 2
def baseEnd_2214428 : Nat := 1137065938774567273966037

theorem tailTrace_2214428 : CollatzResearch.WordTrace tailWord_2214428 prefixEnd_2214428 1137065938774567273966037 := by
  unfold tailWord_2214428
  simp only [CollatzResearch.WordTrace]
  refine ⟨40383412210756512518965969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53844549614342016691954625 40383412210756512518965969)
  ·
    refine ⟨30287559158067384389224477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40383412210756512518965969 30287559158067384389224477)
    ·
      refine ⟨11357834684275269145959179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30287559158067384389224477 11357834684275269145959179)
      ·
        refine ⟨17036752026412903718938769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11357834684275269145959179 17036752026412903718938769)
        ·
          refine ⟨12777564019809677789204077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17036752026412903718938769 12777564019809677789204077)
          ·
            refine ⟨4791586507428629170951529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12777564019809677789204077 4791586507428629170951529)
            ·
              refine ⟨3593689880571471878213647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4791586507428629170951529 3593689880571471878213647)
              ·
                refine ⟨5390534820857207817320471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3593689880571471878213647 5390534820857207817320471)
                ·
                  refine ⟨8085802231285811725980707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5390534820857207817320471 8085802231285811725980707)
                  ·
                    refine ⟨12128703346928717588971061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8085802231285811725980707 12128703346928717588971061)
                    ·
                      refine ⟨1137065938774567273966037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12128703346928717588971061 1137065938774567273966037)
                      ·
                        rfl

theorem cell23_2214428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_2214428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2214428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2214428 prefixEnd_2214428 := by exact prefixLift 2214428
  have htrace : WordTrace (prefixWord ++ tailWord_2214428) baseStart_2214428 baseEnd_2214428 := by
    simpa [prefixWord, tailWord_2214428, baseEnd_2214428] using wordTrace_append hprefix tailTrace_2214428
  have hstable : (prefixWord ++ tailWord_2214428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214428).length < 2 ^ (prefixWord ++ tailWord_2214428).sum := by decide
  have hdescent : baseEnd_2214428 < baseStart_2214428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214436 : List Nat := [2, 3, 1, 5, 1, 1, 3, 2, 1, 1, 3]
def baseStart_2214436 : Nat := 118140960795 + 2214436 * 2 ^ 59
def prefixEnd_2214436 : Nat := 4983230072969 + 3 ^ 40 * 2214436 * 2
def baseEnd_2214436 : Nat := 1137070046619803242666001

theorem tailTrace_2214436 : CollatzResearch.WordTrace tailWord_2214436 prefixEnd_2214436 1137070046619803242666001 := by
  unfold tailWord_2214436
  simp only [CollatzResearch.WordTrace]
  refine ⟨40383558102742021202111581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53844744136989361602815441 40383558102742021202111581)
  ·
    refine ⟨15143834288528257950791843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40383558102742021202111581 15143834288528257950791843)
    ·
      refine ⟨22715751432792386926187765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15143834288528257950791843 22715751432792386926187765)
      ·
        refine ⟨2129601696824286274330103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22715751432792386926187765 2129601696824286274330103)
        ·
          refine ⟨3194402545236429411495155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2129601696824286274330103 3194402545236429411495155)
          ·
            refine ⟨4791603817854644117242733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3194402545236429411495155 4791603817854644117242733)
            ·
              refine ⟨1796851431695491543966025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4791603817854644117242733 1796851431695491543966025)
              ·
                refine ⟨1347638573771618657974519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1796851431695491543966025 1347638573771618657974519)
                ·
                  refine ⟨2021457860657427986961779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1347638573771618657974519 2021457860657427986961779)
                  ·
                    refine ⟨3032186790986141980442669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2021457860657427986961779 3032186790986141980442669)
                    ·
                      refine ⟨1137070046619803242666001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3032186790986141980442669 1137070046619803242666001)
                      ·
                        rfl

theorem cell23_2214436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_2214436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2214436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2214436 prefixEnd_2214436 := by exact prefixLift 2214436
  have htrace : WordTrace (prefixWord ++ tailWord_2214436) baseStart_2214436 baseEnd_2214436 := by
    simpa [prefixWord, tailWord_2214436, baseEnd_2214436] using wordTrace_append hprefix tailTrace_2214436
  have hstable : (prefixWord ++ tailWord_2214436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214436).length < 2 ^ (prefixWord ++ tailWord_2214436).sum := by decide
  have hdescent : baseEnd_2214436 < baseStart_2214436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214442 : List Nat := [3, 1, 4, 1, 1, 2, 3, 1, 3, 2, 2]
def baseStart_2214442 : Nat := 118140960795 + 2214442 * 2 ^ 59
def prefixEnd_2214442 : Nat := 4983230072969 + 3 ^ 40 * 2214442 * 2
def baseEnd_2214442 : Nat := 1137073127503730219190973

theorem tailTrace_2214442 : CollatzResearch.WordTrace tailWord_2214442 prefixEnd_2214442 1137073127503730219190973 := by
  unfold tailWord_2214442
  simp only [CollatzResearch.WordTrace]
  refine ⟨20191833760865576357235395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53844890028974870285961053 20191833760865576357235395)
  ·
    refine ⟨30287750641298364535853093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20191833760865576357235395 30287750641298364535853093)
    ·
      refine ⟨5678953245243443350472455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30287750641298364535853093 5678953245243443350472455)
      ·
        refine ⟨8518429867865165025708683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5678953245243443350472455 8518429867865165025708683)
        ·
          refine ⟨12777644801797747538563025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8518429867865165025708683 12777644801797747538563025)
          ·
            refine ⟨9583233601348310653922269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12777644801797747538563025 9583233601348310653922269)
            ·
              refine ⟨3593712600505616495220851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9583233601348310653922269 3593712600505616495220851)
              ·
                refine ⟨5390568900758424742831277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3593712600505616495220851 5390568900758424742831277)
                ·
                  refine ⟨2021463337784409278561729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5390568900758424742831277 2021463337784409278561729)
                  ·
                    refine ⟨1516097503338306958921297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2021463337784409278561729 1516097503338306958921297)
                    ·
                      refine ⟨1137073127503730219190973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1516097503338306958921297 1137073127503730219190973)
                      ·
                        rfl

theorem cell23_2214442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_2214442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2214442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2214442 prefixEnd_2214442 := by exact prefixLift 2214442
  have htrace : WordTrace (prefixWord ++ tailWord_2214442) baseStart_2214442 baseEnd_2214442 := by
    simpa [prefixWord, tailWord_2214442, baseEnd_2214442] using wordTrace_append hprefix tailTrace_2214442
  have hstable : (prefixWord ++ tailWord_2214442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214442).length < 2 ^ (prefixWord ++ tailWord_2214442).sum := by decide
  have hdescent : baseEnd_2214442 < baseStart_2214442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214462 : List Nat := [4, 2, 1, 4, 1, 1, 1, 1, 3, 2, 3]
def baseStart_2214462 : Nat := 118140960795 + 2214462 * 2 ^ 59
def prefixEnd_2214462 : Nat := 4983230072969 + 3 ^ 40 * 2214462 * 2
def baseEnd_2214462 : Nat := 1137083397116820140940881

theorem tailTrace_2214462 : CollatzResearch.WordTrace tailWord_2214462 prefixEnd_2214462 1137083397116820140940881 := by
  unfold tailWord_2214462
  simp only [CollatzResearch.WordTrace]
  refine ⟨10096008062923731105583705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53845376335593232563113093 10096008062923731105583705)
  ·
    refine ⟨7572006047192798329187779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10096008062923731105583705 7572006047192798329187779)
    ·
      refine ⟨11358009070789197493781669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7572006047192798329187779 11358009070789197493781669)
      ·
        refine ⟨2129626700772974530084063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11358009070789197493781669 2129626700772974530084063)
        ·
          refine ⟨3194440051159461795126095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2129626700772974530084063 3194440051159461795126095)
          ·
            refine ⟨4791660076739192692689143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3194440051159461795126095 4791660076739192692689143)
            ·
              refine ⟨7187490115108789039033715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4791660076739192692689143 7187490115108789039033715)
              ·
                refine ⟨10781235172663183558550573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7187490115108789039033715 10781235172663183558550573)
                ·
                  refine ⟨4042963189748693834456465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10781235172663183558550573 4042963189748693834456465)
                  ·
                    refine ⟨3032222392311520375842349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4042963189748693834456465 3032222392311520375842349)
                    ·
                      refine ⟨1137083397116820140940881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3032222392311520375842349 1137083397116820140940881)
                      ·
                        rfl

theorem cell23_2214462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_2214462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2214462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2214462 prefixEnd_2214462 := by exact prefixLift 2214462
  have htrace : WordTrace (prefixWord ++ tailWord_2214462) baseStart_2214462 baseEnd_2214462 := by
    simpa [prefixWord, tailWord_2214462, baseEnd_2214462] using wordTrace_append hprefix tailTrace_2214462
  have hstable : (prefixWord ++ tailWord_2214462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214462).length < 2 ^ (prefixWord ++ tailWord_2214462).sum := by decide
  have hdescent : baseEnd_2214462 < baseStart_2214462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214485 : List Nat := [1, 3, 2, 2, 1, 1, 2, 5, 1, 3, 2]
def baseStart_2214485 : Nat := 118140960795 + 2214485 * 2 ^ 59
def prefixEnd_2214485 : Nat := 4983230072969 + 3 ^ 40 * 2214485 * 2
def baseEnd_2214485 : Nat := 1137095207171873550953275

theorem tailTrace_2214485 : CollatzResearch.WordTrace tailWord_2214485 prefixEnd_2214485 1137095207171873550953275 := by
  unfold tailWord_2214485
  simp only [CollatzResearch.WordTrace]
  refine ⟨80768903382306523772756909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53845935588204349181837939 80768903382306523772756909)
  ·
    refine ⟨30288338768364946414783841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80768903382306523772756909 30288338768364946414783841)
    ·
      refine ⟨22716254076273709811087881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30288338768364946414783841 22716254076273709811087881)
      ·
        refine ⟨17037190557205282358315911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22716254076273709811087881 17037190557205282358315911)
        ·
          refine ⟨25555785835807923537473867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17037190557205282358315911 25555785835807923537473867)
          ·
            refine ⟨38333678753711885306210801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25555785835807923537473867 38333678753711885306210801)
            ·
              refine ⟨28750259065283913979658101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38333678753711885306210801 28750259065283913979658101)
              ·
                refine ⟨2695336787370366935592947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28750259065283913979658101 2695336787370366935592947)
                ·
                  refine ⟨4043005181055550403389421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2695336787370366935592947 4043005181055550403389421)
                  ·
                    refine ⟨1516126942895831401271033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4043005181055550403389421 1516126942895831401271033)
                    ·
                      refine ⟨1137095207171873550953275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1516126942895831401271033 1137095207171873550953275)
                      ·
                        rfl

theorem cell23_2214485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 5, 1, 3, 2].length) (baseStart_2214485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2214485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2214485 prefixEnd_2214485 := by exact prefixLift 2214485
  have htrace : WordTrace (prefixWord ++ tailWord_2214485) baseStart_2214485 baseEnd_2214485 := by
    simpa [prefixWord, tailWord_2214485, baseEnd_2214485] using wordTrace_append hprefix tailTrace_2214485
  have hstable : (prefixWord ++ tailWord_2214485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214485).length < 2 ^ (prefixWord ++ tailWord_2214485).sum := by decide
  have hdescent : baseEnd_2214485 < baseStart_2214485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214511 : List Nat := [1, 1, 2, 1, 3, 2, 3, 1, 1, 4, 4]
def baseStart_2214511 : Nat := 118140960795 + 2214511 * 2 ^ 59
def prefixEnd_2214511 : Nat := 4983230072969 + 3 ^ 40 * 2214511 * 2
def baseEnd_2214511 : Nat := 1137108557668890449228155

theorem tailTrace_2214511 : CollatzResearch.WordTrace tailWord_2214511 prefixEnd_2214511 1137108557668890449228155 := by
  unfold tailWord_2214511
  simp only [CollatzResearch.WordTrace]
  refine ⟨80769851680212330213203387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53846567786808220142135591 80769851680212330213203387)
  ·
    refine ⟨121154777520318495319805081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80769851680212330213203387 121154777520318495319805081)
    ·
      refine ⟨90866083140238871489853811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121154777520318495319805081 90866083140238871489853811)
      ·
        refine ⟨136299124710358307234780717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90866083140238871489853811 136299124710358307234780717)
        ·
          refine ⟨51112171766384365213042769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136299124710358307234780717 51112171766384365213042769)
          ·
            refine ⟨38334128824788273909782077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51112171766384365213042769 38334128824788273909782077)
            ·
              refine ⟨14375298309295602716168279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38334128824788273909782077 14375298309295602716168279)
              ·
                refine ⟨21562947463943404074252419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14375298309295602716168279 21562947463943404074252419)
                ·
                  refine ⟨32344421195915106111378629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21562947463943404074252419 32344421195915106111378629)
                  ·
                    refine ⟨6064578974234082395883493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32344421195915106111378629 6064578974234082395883493)
                    ·
                      refine ⟨1137108557668890449228155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6064578974234082395883493 1137108557668890449228155)
                      ·
                        rfl

theorem cell23_2214511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 4, 4].length) (baseStart_2214511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2214511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2214511 prefixEnd_2214511 := by exact prefixLift 2214511
  have htrace : WordTrace (prefixWord ++ tailWord_2214511) baseStart_2214511 baseEnd_2214511 := by
    simpa [prefixWord, tailWord_2214511, baseEnd_2214511] using wordTrace_append hprefix tailTrace_2214511
  have hstable : (prefixWord ++ tailWord_2214511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214511).length < 2 ^ (prefixWord ++ tailWord_2214511).sum := by decide
  have hdescent : baseEnd_2214511 < baseStart_2214511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214521 : List Nat := [1, 2, 1, 3, 3, 2, 1, 1, 9]
def baseStart_2214521 : Nat := 118140960795 + 2214521 * 2 ^ 59
def prefixEnd_2214521 : Nat := 4983230072969 + 3 ^ 40 * 2214521 * 2
def baseEnd_2214521 : Nat := 126345965830603934455901

theorem tailTrace_2214521 : CollatzResearch.WordTrace tailWord_2214521 prefixEnd_2214521 126345965830603934455901 := by
  unfold tailWord_2214521
  simp only [CollatzResearch.WordTrace]
  refine ⟨80770216410176101921067417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53846810940117401280711611 80770216410176101921067417)
  ·
    refine ⟨60577662307632076440800563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80770216410176101921067417 60577662307632076440800563)
    ·
      refine ⟨90866493461448114661200845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60577662307632076440800563 90866493461448114661200845)
      ·
        refine ⟨34074935048043042997950317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90866493461448114661200845 34074935048043042997950317)
        ·
          refine ⟨12778100643016141124231369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34074935048043042997950317 12778100643016141124231369)
          ·
            refine ⟨9583575482262105843173527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12778100643016141124231369 9583575482262105843173527)
            ·
              refine ⟨14375363223393158764760291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9583575482262105843173527 14375363223393158764760291)
              ·
                refine ⟨21563044835089738147140437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14375363223393158764760291 21563044835089738147140437)
                ·
                  refine ⟨126345965830603934455901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 21563044835089738147140437 126345965830603934455901)
                  ·
                    rfl

theorem cell23_2214521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 9].length) (baseStart_2214521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2214521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2214521 prefixEnd_2214521 := by exact prefixLift 2214521
  have htrace : WordTrace (prefixWord ++ tailWord_2214521) baseStart_2214521 baseEnd_2214521 := by
    simpa [prefixWord, tailWord_2214521, baseEnd_2214521] using wordTrace_append hprefix tailTrace_2214521
  have hstable : (prefixWord ++ tailWord_2214521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214521).length < 2 ^ (prefixWord ++ tailWord_2214521).sum := by decide
  have hdescent : baseEnd_2214521 < baseStart_2214521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214530 : List Nat := [3, 4, 3, 1, 2, 1, 2, 1, 1, 2, 3]
def baseStart_2214530 : Nat := 118140960795 + 2214530 * 2 ^ 59
def prefixEnd_2214530 : Nat := 4983230072969 + 3 ^ 40 * 2214530 * 2
def baseEnd_2214530 : Nat := 1137118313801325874890569

theorem tailTrace_2214530 : CollatzResearch.WordTrace tailWord_2214530 prefixEnd_2214530 1137118313801325874890569 := by
  unfold tailWord_2214530
  simp only [CollatzResearch.WordTrace]
  refine ⟨20192636166785874114536261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53847029778095664305430029 20192636166785874114536261)
  ·
    refine ⟨3786119281272351396475549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20192636166785874114536261 3786119281272351396475549)
    ·
      refine ⟨1419794730477131773678331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3786119281272351396475549 1419794730477131773678331)
      ·
        refine ⟨2129692095715697660517497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1419794730477131773678331 2129692095715697660517497)
        ·
          refine ⟨1597269071786773245388123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2129692095715697660517497 1597269071786773245388123)
          ·
            refine ⟨2395903607680159868082185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1597269071786773245388123 2395903607680159868082185)
            ·
              refine ⟨1796927705760119901061639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2395903607680159868082185 1796927705760119901061639)
              ·
                refine ⟨2695391558640179851592459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1796927705760119901061639 2695391558640179851592459)
                ·
                  refine ⟨4043087337960269777388689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2695391558640179851592459 4043087337960269777388689)
                  ·
                    refine ⟨3032315503470202333041517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4043087337960269777388689 3032315503470202333041517)
                    ·
                      refine ⟨1137118313801325874890569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3032315503470202333041517 1137118313801325874890569)
                      ·
                        rfl

theorem cell23_2214530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_2214530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2214530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2214530 prefixEnd_2214530 := by exact prefixLift 2214530
  have htrace : WordTrace (prefixWord ++ tailWord_2214530) baseStart_2214530 baseEnd_2214530 := by
    simpa [prefixWord, tailWord_2214530, baseEnd_2214530] using wordTrace_append hprefix tailTrace_2214530
  have hstable : (prefixWord ++ tailWord_2214530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214530).length < 2 ^ (prefixWord ++ tailWord_2214530).sum := by decide
  have hdescent : baseEnd_2214530 < baseStart_2214530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214588 : List Nat := [2, 2, 2, 3, 1, 1, 1, 3, 1, 3, 4]
def baseStart_2214588 : Nat := 118140960795 + 2214588 * 2 ^ 59
def prefixEnd_2214588 : Nat := 4983230072969 + 3 ^ 40 * 2214588 * 2
def baseEnd_2214588 : Nat := 1137148095679286647965301

theorem tailTrace_2214588 : CollatzResearch.WordTrace tailWord_2214588 prefixEnd_2214588 1137148095679286647965301 := by
  unfold tailWord_2214588
  simp only [CollatzResearch.WordTrace]
  refine ⟨40386330050466686181878209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53848440067288914909170945 40386330050466686181878209)
  ·
    refine ⟨30289747537850014636408657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40386330050466686181878209 30289747537850014636408657)
    ·
      refine ⟨22717310653387510977306493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30289747537850014636408657 22717310653387510977306493)
      ·
        refine ⟨8518991495020316616489935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22717310653387510977306493 8518991495020316616489935)
        ·
          refine ⟨12778487242530474924734903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8518991495020316616489935 12778487242530474924734903)
          ·
            refine ⟨19167730863795712387102355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12778487242530474924734903 19167730863795712387102355)
            ·
              refine ⟨28751596295693568580653533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19167730863795712387102355 28751596295693568580653533)
              ·
                refine ⟨10781848610885088217745075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28751596295693568580653533 10781848610885088217745075)
                ·
                  refine ⟨16172772916327632326617613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10781848610885088217745075 16172772916327632326617613)
                  ·
                    refine ⟨6064789843622862122481605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16172772916327632326617613 6064789843622862122481605)
                    ·
                      refine ⟨1137148095679286647965301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6064789843622862122481605 1137148095679286647965301)
                      ·
                        rfl

theorem cell23_2214588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_2214588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2214588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2214588 prefixEnd_2214588 := by exact prefixLift 2214588
  have htrace : WordTrace (prefixWord ++ tailWord_2214588) baseStart_2214588 baseEnd_2214588 := by
    simpa [prefixWord, tailWord_2214588, baseEnd_2214588] using wordTrace_append hprefix tailTrace_2214588
  have hstable : (prefixWord ++ tailWord_2214588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214588).length < 2 ^ (prefixWord ++ tailWord_2214588).sum := by decide
  have hdescent : baseEnd_2214588 < baseStart_2214588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214615 : List Nat := [1, 1, 3, 2, 1, 4, 3, 1, 3, 4]
def baseStart_2214615 : Nat := 118140960795 + 2214615 * 2 ^ 59
def prefixEnd_2214615 : Nat := 4983230072969 + 3 ^ 40 * 2214615 * 2
def baseEnd_2214615 : Nat := 379053986552319347442559

theorem tailTrace_2214615 : CollatzResearch.WordTrace tailWord_2214615 prefixEnd_2214615 379053986552319347442559 := by
  unfold tailWord_2214615
  simp only [CollatzResearch.WordTrace]
  refine ⟨80773644871835555974989299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53849096581223703983326199 80773644871835555974989299)
  ·
    refine ⟨121160467307753333962483949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80773644871835555974989299 121160467307753333962483949)
    ·
      refine ⟨45435175240407500235931481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121160467307753333962483949 45435175240407500235931481)
      ·
        refine ⟨34076381430305625176948611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45435175240407500235931481 34076381430305625176948611)
        ·
          refine ⟨51114572145458437765422917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34076381430305625176948611 51114572145458437765422917)
          ·
            refine ⟨9583982277273457081016797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51114572145458437765422917 9583982277273457081016797)
            ·
              refine ⟨3593993353977546405381299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9583982277273457081016797 3593993353977546405381299)
              ·
                refine ⟨5390990030966319608071949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3593993353977546405381299 5390990030966319608071949)
                ·
                  refine ⟨2021621261612369853026981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5390990030966319608071949 2021621261612369853026981)
                  ·
                    refine ⟨379053986552319347442559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2021621261612369853026981 379053986552319347442559)
                    ·
                      rfl

theorem cell23_2214615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 3, 4].length) (baseStart_2214615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2214615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2214615 prefixEnd_2214615 := by exact prefixLift 2214615
  have htrace : WordTrace (prefixWord ++ tailWord_2214615) baseStart_2214615 baseEnd_2214615 := by
    simpa [prefixWord, tailWord_2214615, baseEnd_2214615] using wordTrace_append hprefix tailTrace_2214615
  have hstable : (prefixWord ++ tailWord_2214615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214615).length < 2 ^ (prefixWord ++ tailWord_2214615).sum := by decide
  have hdescent : baseEnd_2214615 < baseStart_2214615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214642 : List Nat := [3, 2, 1, 3, 1, 3, 2, 1, 2, 2, 3]
def baseStart_2214642 : Nat := 118140960795 + 2214642 * 2 ^ 59
def prefixEnd_2214642 : Nat := 4983230072969 + 3 ^ 40 * 2214642 * 2
def baseEnd_2214642 : Nat := 1137175823634629436690053

theorem tailTrace_2214642 : CollatzResearch.WordTrace tailWord_2214642 prefixEnd_2214642 1137175823634629436690053 := by
  unfold tailWord_2214642
  simp only [CollatzResearch.WordTrace]
  refine ⟨20193657410684434896555545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53849753095158493057481453 20193657410684434896555545)
  ·
    refine ⟨15145243058013326172416659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20193657410684434896555545 15145243058013326172416659)
    ·
      refine ⟨22717864587019989258624989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15145243058013326172416659 22717864587019989258624989)
      ·
        refine ⟨8519199220132495971984371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22717864587019989258624989 8519199220132495971984371)
        ·
          refine ⟨12778798830198743957976557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8519199220132495971984371 12778798830198743957976557)
          ·
            refine ⟨4792049561324528984241209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12778798830198743957976557 4792049561324528984241209)
            ·
              refine ⟨3594037170993396738180907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4792049561324528984241209 3594037170993396738180907)
              ·
                refine ⟨5391055756490095107271361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3594037170993396738180907 5391055756490095107271361)
                ·
                  refine ⟨4043291817367571330453521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5391055756490095107271361 4043291817367571330453521)
                  ·
                    refine ⟨3032468863025678497840141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4043291817367571330453521 3032468863025678497840141)
                    ·
                      refine ⟨1137175823634629436690053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3032468863025678497840141 1137175823634629436690053)
                      ·
                        rfl

theorem cell23_2214642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_2214642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2214642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2214642 prefixEnd_2214642 := by exact prefixLift 2214642
  have htrace : WordTrace (prefixWord ++ tailWord_2214642) baseStart_2214642 baseEnd_2214642 := by
    simpa [prefixWord, tailWord_2214642, baseEnd_2214642] using wordTrace_append hprefix tailTrace_2214642
  have hstable : (prefixWord ++ tailWord_2214642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214642).length < 2 ^ (prefixWord ++ tailWord_2214642).sum := by decide
  have hdescent : baseEnd_2214642 < baseStart_2214642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214705 : List Nat := [1, 2, 2, 3, 2, 1, 2, 2, 4, 4]
def baseStart_2214705 : Nat := 118140960795 + 2214705 * 2 ^ 59
def prefixEnd_2214705 : Nat := 4983230072969 + 3 ^ 40 * 2214705 * 2
def baseEnd_2214705 : Nat := 379069390971954230067421

theorem tailTrace_2214705 : CollatzResearch.WordTrace tailWord_2214705 prefixEnd_2214705 379069390971954230067421 := by
  unfold tailWord_2214705
  simp only [CollatzResearch.WordTrace]
  refine ⟨80776927441509501345765569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53851284961006334230510379 80776927441509501345765569)
  ·
    refine ⟨60582695581132126009324177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80776927441509501345765569 60582695581132126009324177)
    ·
      refine ⟨45437021685849094506993133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60582695581132126009324177 45437021685849094506993133)
      ·
        refine ⟨17038883132193410440122425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45437021685849094506993133 17038883132193410440122425)
        ·
          refine ⟨12779162349145057830091819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17038883132193410440122425 12779162349145057830091819)
          ·
            refine ⟨19168743523717586745137729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12779162349145057830091819 19168743523717586745137729)
            ·
              refine ⟨14376557642788190058853297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19168743523717586745137729 14376557642788190058853297)
              ·
                refine ⟨10782418232091142544139973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14376557642788190058853297 10782418232091142544139973)
                ·
                  refine ⟨2021703418517089227026245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10782418232091142544139973 2021703418517089227026245)
                  ·
                    refine ⟨379069390971954230067421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2021703418517089227026245 379069390971954230067421)
                    ·
                      rfl

theorem cell23_2214705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 4, 4].length) (baseStart_2214705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2214705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2214705 prefixEnd_2214705 := by exact prefixLift 2214705
  have htrace : WordTrace (prefixWord ++ tailWord_2214705) baseStart_2214705 baseEnd_2214705 := by
    simpa [prefixWord, tailWord_2214705, baseEnd_2214705] using wordTrace_append hprefix tailTrace_2214705
  have hstable : (prefixWord ++ tailWord_2214705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214705).length < 2 ^ (prefixWord ++ tailWord_2214705).sum := by decide
  have hdescent : baseEnd_2214705 < baseStart_2214705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214709 : List Nat := [1, 3, 3, 1, 3, 3, 2, 1, 1, 5]
def baseStart_2214709 : Nat := 118140960795 + 2214709 * 2 ^ 59
def prefixEnd_2214709 : Nat := 4983230072969 + 3 ^ 40 * 2214709 * 2
def baseEnd_2214709 : Nat := 379070075612826891517415

theorem tailTrace_2214709 : CollatzResearch.WordTrace tailWord_2214709 prefixEnd_2214709 379070075612826891517415 := by
  unfold tailWord_2214709
  simp only [CollatzResearch.WordTrace]
  refine ⟨80777073333495010028911181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53851382222330006685940787 80777073333495010028911181)
  ·
    refine ⟨30291402500060628760841693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80777073333495010028911181 30291402500060628760841693)
    ·
      refine ⟨11359275937522735785315635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30291402500060628760841693 11359275937522735785315635)
      ·
        refine ⟨17038913906284103677973453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11359275937522735785315635 17038913906284103677973453)
        ·
          refine ⟨6389592714856538879240045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17038913906284103677973453 6389592714856538879240045)
          ·
            refine ⟨2396097268071202079715017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6389592714856538879240045 2396097268071202079715017)
            ·
              refine ⟨1797072951053401559786263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2396097268071202079715017 1797072951053401559786263)
              ·
                refine ⟨2695609426580102339679395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1797072951053401559786263 2695609426580102339679395)
                ·
                  refine ⟨4043414139870153509519093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2695609426580102339679395 4043414139870153509519093)
                  ·
                    refine ⟨379070075612826891517415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4043414139870153509519093 379070075612826891517415)
                    ·
                      rfl

theorem cell23_2214709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_2214709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2214709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2214709 prefixEnd_2214709 := by exact prefixLift 2214709
  have htrace : WordTrace (prefixWord ++ tailWord_2214709) baseStart_2214709 baseEnd_2214709 := by
    simpa [prefixWord, tailWord_2214709, baseEnd_2214709] using wordTrace_append hprefix tailTrace_2214709
  have hstable : (prefixWord ++ tailWord_2214709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214709).length < 2 ^ (prefixWord ++ tailWord_2214709).sum := by decide
  have hdescent : baseEnd_2214709 < baseStart_2214709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214712 : List Nat := [2, 1, 2, 1, 3, 2, 1, 2, 5, 2, 2]
def baseStart_2214712 : Nat := 118140960795 + 2214712 * 2 ^ 59
def prefixEnd_2214712 : Nat := 4983230072969 + 3 ^ 40 * 2214712 * 2
def baseEnd_2214712 : Nat := 1137211767280444162814731

theorem tailTrace_2214712 : CollatzResearch.WordTrace tailWord_2214712 prefixEnd_2214712 1137211767280444162814731 := by
  unfold tailWord_2214712
  simp only [CollatzResearch.WordTrace]
  refine ⟨40388591376242070770635195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53851455168322761027513593 40388591376242070770635195)
  ·
    refine ⟨60582887064363106155952793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40388591376242070770635195 60582887064363106155952793)
    ·
      refine ⟨45437165298272329616964595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60582887064363106155952793 45437165298272329616964595)
      ·
        refine ⟨68155747947408494425446893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45437165298272329616964595 68155747947408494425446893)
        ·
          refine ⟨25558405480278185409542585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68155747947408494425446893 25558405480278185409542585)
          ·
            refine ⟨19168804110208639057156939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25558405480278185409542585 19168804110208639057156939)
            ·
              refine ⟨28753206165312958585735409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19168804110208639057156939 28753206165312958585735409)
              ·
                refine ⟨21564904623984718939301557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28753206165312958585735409 21564904623984718939301557)
                ·
                  refine ⟨2021709808498567400559521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21564904623984718939301557 2021709808498567400559521)
                  ·
                    refine ⟨1516282356373925550419641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2021709808498567400559521 1516282356373925550419641)
                    ·
                      refine ⟨1137211767280444162814731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1516282356373925550419641 1137211767280444162814731)
                      ·
                        rfl

theorem cell23_2214712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 5, 2, 2].length) (baseStart_2214712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2214712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2214712 prefixEnd_2214712 := by exact prefixLift 2214712
  have htrace : WordTrace (prefixWord ++ tailWord_2214712) baseStart_2214712 baseEnd_2214712 := by
    simpa [prefixWord, tailWord_2214712, baseEnd_2214712] using wordTrace_append hprefix tailTrace_2214712
  have hstable : (prefixWord ++ tailWord_2214712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214712).length < 2 ^ (prefixWord ++ tailWord_2214712).sum := by decide
  have hdescent : baseEnd_2214712 < baseStart_2214712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214729 : List Nat := [1, 2, 1, 1, 2, 6, 2, 1, 3, 2, 2]
def baseStart_2214729 : Nat := 118140960795 + 2214729 * 2 ^ 59
def prefixEnd_2214729 : Nat := 4983230072969 + 3 ^ 40 * 2214729 * 2
def baseEnd_2214729 : Nat := 1137220496451570596302153

theorem tailTrace_2214729 : CollatzResearch.WordTrace tailWord_2214729 prefixEnd_2214729 1137220496451570596302153 := by
  unfold tailWord_2214729
  simp only [CollatzResearch.WordTrace]
  refine ⟨80777802793422553444639241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53851868528948368963092827 80777802793422553444639241)
  ·
    refine ⟨60583352095066915083479431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80777802793422553444639241 60583352095066915083479431)
    ·
      refine ⟨90875028142600372625219147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60583352095066915083479431 90875028142600372625219147)
      ·
        refine ⟨136312542213900558937828721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90875028142600372625219147 136312542213900558937828721)
        ·
          refine ⟨102234406660425419203371541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136312542213900558937828721 102234406660425419203371541)
          ·
            refine ⟨4792237812207441525158041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 102234406660425419203371541 4792237812207441525158041)
            ·
              refine ⟨3594178359155581143868531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4792237812207441525158041 3594178359155581143868531)
              ·
                refine ⟨5391267538733371715802797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3594178359155581143868531 5391267538733371715802797)
                ·
                  refine ⟨2021725327025014393426049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5391267538733371715802797 2021725327025014393426049)
                  ·
                    refine ⟨1516293995268760795069537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2021725327025014393426049 1516293995268760795069537)
                    ·
                      refine ⟨1137220496451570596302153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1516293995268760795069537 1137220496451570596302153)
                      ·
                        rfl

theorem cell23_2214729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 3, 2, 2].length) (baseStart_2214729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2214729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2214729 prefixEnd_2214729 := by exact prefixLift 2214729
  have htrace : WordTrace (prefixWord ++ tailWord_2214729) baseStart_2214729 baseEnd_2214729 := by
    simpa [prefixWord, tailWord_2214729, baseEnd_2214729] using wordTrace_append hprefix tailTrace_2214729
  have hstable : (prefixWord ++ tailWord_2214729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214729).length < 2 ^ (prefixWord ++ tailWord_2214729).sum := by decide
  have hdescent : baseEnd_2214729 < baseStart_2214729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214805 : List Nat := [1, 3, 2, 1, 1, 4, 1, 2, 2, 1, 5]
def baseStart_2214805 : Nat := 118140960795 + 2214805 * 2 ^ 59
def prefixEnd_2214805 : Nat := 4983230072969 + 3 ^ 40 * 2214805 * 2
def baseEnd_2214805 : Nat := 1137259520981312298951803

theorem tailTrace_2214805 : CollatzResearch.WordTrace tailWord_2214805 prefixEnd_2214805 1137259520981312298951803 := by
  unfold tailWord_2214805
  simp only [CollatzResearch.WordTrace]
  refine ⟨80780574741147218424405869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53853716494098145616270579 80780574741147218424405869)
  ·
    refine ⟨30292715527930206909152201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80780574741147218424405869 30292715527930206909152201)
    ·
      refine ⟨22719536645947655181864151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30292715527930206909152201 22719536645947655181864151)
      ·
        refine ⟨34079304968921482772796227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22719536645947655181864151 34079304968921482772796227)
        ·
          refine ⟨51118957453382224159194341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34079304968921482772796227 51118957453382224159194341)
          ·
            refine ⟨9584804522509167029848939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51118957453382224159194341 9584804522509167029848939)
            ·
              refine ⟨14377206783763750544773409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9584804522509167029848939 14377206783763750544773409)
              ·
                refine ⟨10782905087822812908580057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14377206783763750544773409 10782905087822812908580057)
                ·
                  refine ⟨8087178815867109681435043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10782905087822812908580057 8087178815867109681435043)
                  ·
                    refine ⟨12130768223800664522152565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8087178815867109681435043 12130768223800664522152565)
                    ·
                      refine ⟨1137259520981312298951803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12130768223800664522152565 1137259520981312298951803)
                      ·
                        rfl

theorem cell23_2214805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_2214805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2214805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2214805 prefixEnd_2214805 := by exact prefixLift 2214805
  have htrace : WordTrace (prefixWord ++ tailWord_2214805) baseStart_2214805 baseEnd_2214805 := by
    simpa [prefixWord, tailWord_2214805, baseEnd_2214805] using wordTrace_append hprefix tailTrace_2214805
  have hstable : (prefixWord ++ tailWord_2214805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214805).length < 2 ^ (prefixWord ++ tailWord_2214805).sum := by decide
  have hdescent : baseEnd_2214805 < baseStart_2214805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214823 : List Nat := [1, 1, 6, 1, 3, 1, 3, 1, 1, 3, 2]
def baseStart_2214823 : Nat := 118140960795 + 2214823 * 2 ^ 59
def prefixEnd_2214823 : Nat := 4983230072969 + 3 ^ 40 * 2214823 * 2
def baseEnd_2214823 : Nat := 1137268763633093228526721

theorem tailTrace_2214823 : CollatzResearch.WordTrace tailWord_2214823 prefixEnd_2214823 1137268763633093228526721 := by
  unfold tailWord_2214823
  simp only [CollatzResearch.WordTrace]
  refine ⟨80781231255082007498561123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53854154170054671665707415 80781231255082007498561123)
  ·
    refine ⟨121171846882623011247841685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80781231255082007498561123 121171846882623011247841685)
    ·
      refine ⟨5679930322622953652242579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 121171846882623011247841685 5679930322622953652242579)
      ·
        refine ⟨8519895483934430478363869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5679930322622953652242579 8519895483934430478363869)
        ·
          refine ⟨3194960806475411429386451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8519895483934430478363869 3194960806475411429386451)
          ·
            refine ⟨4792441209713117144079677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3194960806475411429386451 4792441209713117144079677)
            ·
              refine ⟨1797165453642418929029879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4792441209713117144079677 1797165453642418929029879)
              ·
                refine ⟨2695748180463628393544819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1797165453642418929029879 2695748180463628393544819)
                ·
                  refine ⟨4043622270695442590317229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2695748180463628393544819 4043622270695442590317229)
                  ·
                    refine ⟨1516358351510790971368961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4043622270695442590317229 1516358351510790971368961)
                    ·
                      refine ⟨1137268763633093228526721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1516358351510790971368961 1137268763633093228526721)
                      ·
                        rfl

theorem cell23_2214823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_2214823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2214823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2214823 prefixEnd_2214823 := by exact prefixLift 2214823
  have htrace : WordTrace (prefixWord ++ tailWord_2214823) baseStart_2214823 baseEnd_2214823 := by
    simpa [prefixWord, tailWord_2214823, baseEnd_2214823] using wordTrace_append hprefix tailTrace_2214823
  have hstable : (prefixWord ++ tailWord_2214823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214823).length < 2 ^ (prefixWord ++ tailWord_2214823).sum := by decide
  have hdescent : baseEnd_2214823 < baseStart_2214823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214842 : List Nat := [3, 1, 1, 1, 2, 1, 5, 4, 5]
def baseStart_2214842 : Nat := 118140960795 + 2214842 * 2 ^ 59
def prefixEnd_2214842 : Nat := 4983230072969 + 3 ^ 40 * 2214842 * 2
def baseEnd_2214842 : Nat := 126364279973947628243237

theorem tailTrace_2214842 : CollatzResearch.WordTrace tailWord_2214842 prefixEnd_2214842 126364279973947628243237 := by
  unfold tailWord_2214842
  simp only [CollatzResearch.WordTrace]
  refine ⟨20195481060503293435875695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53854616161342115829001853 20195481060503293435875695)
  ·
    refine ⟨30293221590754940153813543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20195481060503293435875695 30293221590754940153813543)
    ·
      refine ⟨45439832386132410230720315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30293221590754940153813543 45439832386132410230720315)
      ·
        refine ⟨68159748579198615346080473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45439832386132410230720315 68159748579198615346080473)
        ·
          refine ⟨51119811434398961509560355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68159748579198615346080473 51119811434398961509560355)
          ·
            refine ⟨76679717151598442264340533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51119811434398961509560355 76679717151598442264340533)
            ·
              refine ⟨7188723482962353962281925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76679717151598442264340533 7188723482962353962281925)
              ·
                refine ⟨1347885653055441367927861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7188723482962353962281925 1347885653055441367927861)
                ·
                  refine ⟨126364279973947628243237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1347885653055441367927861 126364279973947628243237)
                  ·
                    rfl

theorem cell23_2214842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 4, 5].length) (baseStart_2214842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2214842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2214842 prefixEnd_2214842 := by exact prefixLift 2214842
  have htrace : WordTrace (prefixWord ++ tailWord_2214842) baseStart_2214842 baseEnd_2214842 := by
    simpa [prefixWord, tailWord_2214842, baseEnd_2214842] using wordTrace_append hprefix tailTrace_2214842
  have hstable : (prefixWord ++ tailWord_2214842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214842).length < 2 ^ (prefixWord ++ tailWord_2214842).sum := by decide
  have hdescent : baseEnd_2214842 < baseStart_2214842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214855 : List Nat := [1, 1, 4, 1, 1, 2, 2, 2, 4, 5]
def baseStart_2214855 : Nat := 118140960795 + 2214855 * 2 ^ 59
def prefixEnd_2214855 : Nat := 4983230072969 + 3 ^ 40 * 2214855 * 2
def baseEnd_2214855 : Nat := 379095065004679034442191

theorem tailTrace_2214855 : CollatzResearch.WordTrace tailWord_2214855 prefixEnd_2214855 379095065004679034442191 := by
  unfold tailWord_2214855
  simp only [CollatzResearch.WordTrace]
  refine ⟨80782398390966076963726019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53854932260644051309150679 80782398390966076963726019)
  ·
    refine ⟨121173597586449115445589029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80782398390966076963726019 121173597586449115445589029)
    ·
      refine ⟨22720049547459209146047943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121173597586449115445589029 22720049547459209146047943)
      ·
        refine ⟨34080074321188813719071915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22720049547459209146047943 34080074321188813719071915)
        ·
          refine ⟨51120111481783220578607873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34080074321188813719071915 51120111481783220578607873)
          ·
            refine ⟨38340083611337415433955905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51120111481783220578607873 38340083611337415433955905)
            ·
              refine ⟨28755062708503061575466929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38340083611337415433955905 28755062708503061575466929)
              ·
                refine ⟨21566297031377296181600197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28755062708503061575466929 21566297031377296181600197)
                ·
                  refine ⟨4043680693383243034050037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21566297031377296181600197 4043680693383243034050037)
                  ·
                    refine ⟨379095065004679034442191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4043680693383243034050037 379095065004679034442191)
                    ·
                      rfl

theorem cell23_2214855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 4, 5].length) (baseStart_2214855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2214855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2214855 prefixEnd_2214855 := by exact prefixLift 2214855
  have htrace : WordTrace (prefixWord ++ tailWord_2214855) baseStart_2214855 baseEnd_2214855 := by
    simpa [prefixWord, tailWord_2214855, baseEnd_2214855] using wordTrace_append hprefix tailTrace_2214855
  have hstable : (prefixWord ++ tailWord_2214855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214855).length < 2 ^ (prefixWord ++ tailWord_2214855).sum := by decide
  have hdescent : baseEnd_2214855 < baseStart_2214855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214872 : List Nat := [2, 1, 2, 2, 2, 3, 3, 1, 2, 5]
def baseStart_2214872 : Nat := 118140960795 + 2214872 * 2 ^ 59
def prefixEnd_2214872 : Nat := 4983230072969 + 3 ^ 40 * 2214872 * 2
def baseEnd_2214872 : Nat := 379097974728387845604665

theorem tailTrace_2214872 : CollatzResearch.WordTrace tailWord_2214872 prefixEnd_2214872 379097974728387845604665 := by
  unfold tailWord_2214872
  simp only [CollatzResearch.WordTrace]
  refine ⟨40391509215952244433547435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53855345621269659244729913 40391509215952244433547435)
  ·
    refine ⟨60587263823928366650321153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40391509215952244433547435 60587263823928366650321153)
    ·
      refine ⟨45440447867946274987740865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60587263823928366650321153 45440447867946274987740865)
      ·
        refine ⟨34080335900959706240805649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45440447867946274987740865 34080335900959706240805649)
        ·
          refine ⟨25560251925719779680604237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34080335900959706240805649 25560251925719779680604237)
          ·
            refine ⟨9585094472144917380226589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25560251925719779680604237 9585094472144917380226589)
            ·
              refine ⟨3594410427054344017584971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9585094472144917380226589 3594410427054344017584971)
              ·
                refine ⟨5391615640581516026377457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3594410427054344017584971 5391615640581516026377457)
                ·
                  refine ⟨4043711730436137019783093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5391615640581516026377457 4043711730436137019783093)
                  ·
                    refine ⟨379097974728387845604665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4043711730436137019783093 379097974728387845604665)
                    ·
                      rfl

theorem cell23_2214872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 2, 5].length) (baseStart_2214872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2214872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2214872 prefixEnd_2214872 := by exact prefixLift 2214872
  have htrace : WordTrace (prefixWord ++ tailWord_2214872) baseStart_2214872 baseEnd_2214872 := by
    simpa [prefixWord, tailWord_2214872, baseEnd_2214872] using wordTrace_append hprefix tailTrace_2214872
  have hstable : (prefixWord ++ tailWord_2214872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214872).length < 2 ^ (prefixWord ++ tailWord_2214872).sum := by decide
  have hdescent : baseEnd_2214872 < baseStart_2214872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214905 : List Nat := [1, 2, 1, 3, 1, 3, 1, 2, 2, 1, 6]
def baseStart_2214905 : Nat := 118140960795 + 2214905 * 2 ^ 59
def prefixEnd_2214905 : Nat := 4983230072969 + 3 ^ 40 * 2214905 * 2
def baseEnd_2214905 : Nat := 1137310869046761907701343

theorem tailTrace_2214905 : CollatzResearch.WordTrace tailWord_2214905 prefixEnd_2214905 1137310869046761907701343 := by
  unfold tailWord_2214905
  simp only [CollatzResearch.WordTrace]
  refine ⟨80784222040784935503046169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53856148027189957002030779 80784222040784935503046169)
  ·
    refine ⟨60588166530588701627284627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80784222040784935503046169 60588166530588701627284627)
    ·
      refine ⟨90882249795883052440926941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60588166530588701627284627 90882249795883052440926941)
      ·
        refine ⟨34080843673456144665347603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90882249795883052440926941 34080843673456144665347603)
        ·
          refine ⟨51121265510184216998021405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34080843673456144665347603 51121265510184216998021405)
          ·
            refine ⟨19170474566319081374258027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51121265510184216998021405 19170474566319081374258027)
            ·
              refine ⟨28755711849478622061387041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19170474566319081374258027 28755711849478622061387041)
              ·
                refine ⟨21566783887108966546040281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28755711849478622061387041 21566783887108966546040281)
                ·
                  refine ⟨16175087915331724909530211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21566783887108966546040281 16175087915331724909530211)
                  ·
                    refine ⟨24262631872997587364295317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16175087915331724909530211 24262631872997587364295317)
                    ·
                      refine ⟨1137310869046761907701343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24262631872997587364295317 1137310869046761907701343)
                      ·
                        rfl

theorem cell23_2214905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_2214905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2214905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2214905 prefixEnd_2214905 := by exact prefixLift 2214905
  have htrace : WordTrace (prefixWord ++ tailWord_2214905) baseStart_2214905 baseEnd_2214905 := by
    simpa [prefixWord, tailWord_2214905, baseEnd_2214905] using wordTrace_append hprefix tailTrace_2214905
  have hstable : (prefixWord ++ tailWord_2214905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214905).length < 2 ^ (prefixWord ++ tailWord_2214905).sum := by decide
  have hdescent : baseEnd_2214905 < baseStart_2214905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214936 : List Nat := [2, 1, 2, 3, 2, 2, 3, 3, 1, 4]
def baseStart_2214936 : Nat := 118140960795 + 2214936 * 2 ^ 59
def prefixEnd_2214936 : Nat := 4983230072969 + 3 ^ 40 * 2214936 * 2
def baseEnd_2214936 : Nat := 379108928982350428804567

theorem tailTrace_2214936 : CollatzResearch.WordTrace tailWord_2214936 prefixEnd_2214936 379108928982350428804567 := by
  unfold tailWord_2214936
  simp only [CollatzResearch.WordTrace]
  refine ⟨40392676351836313898712331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53856901802448418531616441 40392676351836313898712331)
  ·
    refine ⟨60589014527754470848068497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40392676351836313898712331 60589014527754470848068497)
    ·
      refine ⟨45441760895815853136051373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60589014527754470848068497 45441760895815853136051373)
      ·
        refine ⟨17040660335930944926019265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45441760895815853136051373 17040660335930944926019265)
        ·
          refine ⟨12780495251948208694514449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17040660335930944926019265 12780495251948208694514449)
          ·
            refine ⟨9585371438961156520885837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12780495251948208694514449 9585371438961156520885837)
            ·
              refine ⟨3594514289610433695332189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9585371438961156520885837 3594514289610433695332189)
              ·
                refine ⟨1347942858603912635749571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3594514289610433695332189 1347942858603912635749571)
                ·
                  refine ⟨2021914287905868953624357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1347942858603912635749571 2021914287905868953624357)
                  ·
                    refine ⟨379108928982350428804567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2021914287905868953624357 379108928982350428804567)
                    ·
                      rfl

theorem cell23_2214936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 3, 1, 4].length) (baseStart_2214936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2214936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2214936 prefixEnd_2214936 := by exact prefixLift 2214936
  have htrace : WordTrace (prefixWord ++ tailWord_2214936) baseStart_2214936 baseEnd_2214936 := by
    simpa [prefixWord, tailWord_2214936, baseEnd_2214936] using wordTrace_append hprefix tailTrace_2214936
  have hstable : (prefixWord ++ tailWord_2214936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214936).length < 2 ^ (prefixWord ++ tailWord_2214936).sum := by decide
  have hdescent : baseEnd_2214936 < baseStart_2214936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214962 : List Nat := [3, 2, 1, 1, 2, 2, 2, 2, 3, 5]
def baseStart_2214962 : Nat := 118140960795 + 2214962 * 2 ^ 59
def prefixEnd_2214962 : Nat := 4983230072969 + 3 ^ 40 * 2214962 * 2
def baseEnd_2214962 : Nat := 379113379148022728229527

theorem tailTrace_2214962 : CollatzResearch.WordTrace tailWord_2214962 prefixEnd_2214962 379113379148022728229527 := by
  unfold tailWord_2214962
  simp only [CollatzResearch.WordTrace]
  refine ⟨20196575250394608559467785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53857534001052289491914093 20196575250394608559467785)
  ·
    refine ⟨15147431437795956419600839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20196575250394608559467785 15147431437795956419600839)
    ·
      refine ⟨22721147156693934629401259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15147431437795956419600839 22721147156693934629401259)
      ·
        refine ⟨34081720735040901944101889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22721147156693934629401259 34081720735040901944101889)
        ·
          refine ⟨25561290551280676458076417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34081720735040901944101889 25561290551280676458076417)
          ·
            refine ⟨19170967913460507343557313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25561290551280676458076417 19170967913460507343557313)
            ·
              refine ⟨14378225935095380507667985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19170967913460507343557313 14378225935095380507667985)
              ·
                refine ⟨10783669451321535380750989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14378225935095380507667985 10783669451321535380750989)
                ·
                  refine ⟨4043876044245575767781621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10783669451321535380750989 4043876044245575767781621)
                  ·
                    refine ⟨379113379148022728229527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4043876044245575767781621 379113379148022728229527)
                    ·
                      rfl

theorem cell23_2214962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 3, 5].length) (baseStart_2214962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2214962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2214962 prefixEnd_2214962 := by exact prefixLift 2214962
  have htrace : WordTrace (prefixWord ++ tailWord_2214962) baseStart_2214962 baseEnd_2214962 := by
    simpa [prefixWord, tailWord_2214962, baseEnd_2214962] using wordTrace_append hprefix tailTrace_2214962
  have hstable : (prefixWord ++ tailWord_2214962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214962).length < 2 ^ (prefixWord ++ tailWord_2214962).sum := by decide
  have hdescent : baseEnd_2214962 < baseStart_2214962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214966 : List Nat := [5, 1, 2, 1, 1, 2, 4, 1, 6]
def baseStart_2214966 : Nat := 118140960795 + 2214966 * 2 ^ 59
def prefixEnd_2214966 : Nat := 4983230072969 + 3 ^ 40 * 2214966 * 2
def baseEnd_2214966 : Nat := 126371354596298463226507

theorem tailTrace_2214966 : CollatzResearch.WordTrace tailWord_2214966 prefixEnd_2214966 126371354596298463226507 := by
  unfold tailWord_2214966
  simp only [CollatzResearch.WordTrace]
  refine ⟨5049152930847746432563547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53857631262375961947344501 5049152930847746432563547)
  ·
    refine ⟨7573729396271619648845321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5049152930847746432563547 7573729396271619648845321)
    ·
      refine ⟨5680297047203714736633991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7573729396271619648845321 5680297047203714736633991)
      ·
        refine ⟨8520445570805572104950987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5680297047203714736633991 8520445570805572104950987)
        ·
          refine ⟨12780668356208358157426481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8520445570805572104950987 12780668356208358157426481)
          ·
            refine ⟨9585501267156268618069861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12780668356208358157426481 9585501267156268618069861)
            ·
              refine ⟨1797281487591800365888099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9585501267156268618069861 1797281487591800365888099)
              ·
                refine ⟨2695922231387700548832149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1797281487591800365888099 2695922231387700548832149)
                ·
                  refine ⟨126371354596298463226507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2695922231387700548832149 126371354596298463226507)
                  ·
                    rfl

theorem cell23_2214966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 1, 6].length) (baseStart_2214966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2214966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2214966 prefixEnd_2214966 := by exact prefixLift 2214966
  have htrace : WordTrace (prefixWord ++ tailWord_2214966) baseStart_2214966 baseEnd_2214966 := by
    simpa [prefixWord, tailWord_2214966, baseEnd_2214966] using wordTrace_append hprefix tailTrace_2214966
  have hstable : (prefixWord ++ tailWord_2214966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214966).length < 2 ^ (prefixWord ++ tailWord_2214966).sum := by decide
  have hdescent : baseEnd_2214966 < baseStart_2214966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2214992 : List Nat := [2, 1, 1, 1, 1, 3, 1, 3, 6, 4]
def baseStart_2214992 : Nat := 118140960795 + 2214992 * 2 ^ 59
def prefixEnd_2214992 : Nat := 4983230072969 + 3 ^ 40 * 2214992 * 2
def baseEnd_2214992 : Nat := 379118513954567689104481

theorem tailTrace_2214992 : CollatzResearch.WordTrace tailWord_2214992 prefixEnd_2214992 379118513954567689104481 := by
  unfold tailWord_2214992
  simp only [CollatzResearch.WordTrace]
  refine ⟨40393697595734874680731615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53858263460979832907642153 40393697595734874680731615)
  ·
    refine ⟨60590546393602312021097423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40393697595734874680731615 60590546393602312021097423)
    ·
      refine ⟨90885819590403468031646135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60590546393602312021097423 90885819590403468031646135)
      ·
        refine ⟨136328729385605202047469203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90885819590403468031646135 136328729385605202047469203)
        ·
          refine ⟨204493094078407803071203805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136328729385605202047469203 204493094078407803071203805)
          ·
            refine ⟨76684910279402926151701427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 204493094078407803071203805 76684910279402926151701427)
            ·
              refine ⟨115027365419104389227552141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76684910279402926151701427 115027365419104389227552141)
              ·
                refine ⟨43135262032164145960332053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115027365419104389227552141 43135262032164145960332053)
                ·
                  refine ⟨2021965407757694341890565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 43135262032164145960332053 2021965407757694341890565)
                  ·
                    refine ⟨379118513954567689104481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2021965407757694341890565 379118513954567689104481)
                    ·
                      rfl

theorem cell23_2214992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 6, 4].length) (baseStart_2214992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2214992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2214992 prefixEnd_2214992 := by exact prefixLift 2214992
  have htrace : WordTrace (prefixWord ++ tailWord_2214992) baseStart_2214992 baseEnd_2214992 := by
    simpa [prefixWord, tailWord_2214992, baseEnd_2214992] using wordTrace_append hprefix tailTrace_2214992
  have hstable : (prefixWord ++ tailWord_2214992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2214992).length < 2 ^ (prefixWord ++ tailWord_2214992).sum := by decide
  have hdescent : baseEnd_2214992 < baseStart_2214992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2214992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215002 : List Nat := [3, 1, 1, 2, 1, 1, 2, 5, 1, 1, 5]
def baseStart_2215002 : Nat := 118140960795 + 2215002 * 2 ^ 59
def prefixEnd_2215002 : Nat := 4983230072969 + 3 ^ 40 * 2215002 * 2
def baseEnd_2215002 : Nat := 1137360676670248028188397

theorem tailTrace_2215002 : CollatzResearch.WordTrace tailWord_2215002 prefixEnd_2215002 1137360676670248028188397 := by
  unfold tailWord_2215002
  simp only [CollatzResearch.WordTrace]
  refine ⟨20196939980358380267331815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53858506614289014046218173 20196939980358380267331815)
  ·
    refine ⟨30295409970537570400997723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20196939980358380267331815 30295409970537570400997723)
    ·
      refine ⟨45443114955806355601496585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30295409970537570400997723 45443114955806355601496585)
      ·
        refine ⟨34082336216854766701122439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45443114955806355601496585 34082336216854766701122439)
        ·
          refine ⟨51123504325282150051683659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34082336216854766701122439 51123504325282150051683659)
          ·
            refine ⟨76685256487923225077525489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51123504325282150051683659 76685256487923225077525489)
            ·
              refine ⟨57513942365942418808144117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76685256487923225077525489 57513942365942418808144117)
              ·
                refine ⟨5391932096807101763263511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57513942365942418808144117 5391932096807101763263511)
                ·
                  refine ⟨8087898145210652644895267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5391932096807101763263511 8087898145210652644895267)
                  ·
                    refine ⟨12131847217815978967342901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8087898145210652644895267 12131847217815978967342901)
                    ·
                      refine ⟨1137360676670248028188397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12131847217815978967342901 1137360676670248028188397)
                      ·
                        rfl

theorem cell23_2215002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_2215002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215002 prefixEnd_2215002 := by exact prefixLift 2215002
  have htrace : WordTrace (prefixWord ++ tailWord_2215002) baseStart_2215002 baseEnd_2215002 := by
    simpa [prefixWord, tailWord_2215002, baseEnd_2215002] using wordTrace_append hprefix tailTrace_2215002
  have hstable : (prefixWord ++ tailWord_2215002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215002).length < 2 ^ (prefixWord ++ tailWord_2215002).sum := by decide
  have hdescent : baseEnd_2215002 < baseStart_2215002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215009 : List Nat := [1, 2, 3, 1, 1, 2, 3, 4, 2, 4]
def baseStart_2215009 : Nat := 118140960795 + 2215009 * 2 ^ 59
def prefixEnd_2215009 : Nat := 4983230072969 + 3 ^ 40 * 2215009 * 2
def baseEnd_2215009 : Nat := 379121423678276500266955

theorem tailTrace_2215009 : CollatzResearch.WordTrace tailWord_2215009 prefixEnd_2215009 379121423678276500266955 := by
  unfold tailWord_2215009
  simp only [CollatzResearch.WordTrace]
  refine ⟨80788015232408161264832081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53858676821605440843221387 80788015232408161264832081)
  ·
    refine ⟨60591011424306120948624061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80788015232408161264832081 60591011424306120948624061)
    ·
      refine ⟨22721629284114795355734023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60591011424306120948624061 22721629284114795355734023)
      ·
        refine ⟨34082443926172193033601035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22721629284114795355734023 34082443926172193033601035)
        ·
          refine ⟨51123665889258289550401553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34082443926172193033601035 51123665889258289550401553)
          ·
            refine ⟨38342749416943717162801165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51123665889258289550401553 38342749416943717162801165)
            ·
              refine ⟨14378531031353893936050437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38342749416943717162801165 14378531031353893936050437)
              ·
                refine ⟨2695974568378855113009457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14378531031353893936050437 2695974568378855113009457)
                ·
                  refine ⟨2021980926284141334757093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2695974568378855113009457 2021980926284141334757093)
                  ·
                    refine ⟨379121423678276500266955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2021980926284141334757093 379121423678276500266955)
                    ·
                      rfl

theorem cell23_2215009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 4, 2, 4].length) (baseStart_2215009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215009 prefixEnd_2215009 := by exact prefixLift 2215009
  have htrace : WordTrace (prefixWord ++ tailWord_2215009) baseStart_2215009 baseEnd_2215009 := by
    simpa [prefixWord, tailWord_2215009, baseEnd_2215009] using wordTrace_append hprefix tailTrace_2215009
  have hstable : (prefixWord ++ tailWord_2215009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215009).length < 2 ^ (prefixWord ++ tailWord_2215009).sum := by decide
  have hdescent : baseEnd_2215009 < baseStart_2215009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215010 : List Nat := [3, 3, 2, 2, 1, 2, 1, 4, 1, 1, 3]
def baseStart_2215010 : Nat := 118140960795 + 2215010 * 2 ^ 59
def prefixEnd_2215010 : Nat := 4983230072969 + 3 ^ 40 * 2215010 * 2
def baseEnd_2215010 : Nat := 1137364784515483996888361

theorem tailTrace_2215010 : CollatzResearch.WordTrace tailWord_2215010 prefixEnd_2215010 1137364784515483996888361 := by
  unfold tailWord_2215010
  simp only [CollatzResearch.WordTrace]
  refine ⟨20197012926351134608904621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53858701136936358957078989 20197012926351134608904621)
  ·
    refine ⟨7573879847381675478339233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20197012926351134608904621 7573879847381675478339233)
    ·
      refine ⟨5680409885536256608754425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7573879847381675478339233 5680409885536256608754425)
      ·
        refine ⟨4260307414152192456565819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5680409885536256608754425 4260307414152192456565819)
        ·
          refine ⟨6390461121228288684848729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4260307414152192456565819 6390461121228288684848729)
          ·
            refine ⟨4792845840921216513636547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6390461121228288684848729 4792845840921216513636547)
            ·
              refine ⟨7189268761381824770454821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4792845840921216513636547 7189268761381824770454821)
              ·
                refine ⟨1347987892759092144460279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7189268761381824770454821 1347987892759092144460279)
                ·
                  refine ⟨2021981839138638216690419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1347987892759092144460279 2021981839138638216690419)
                  ·
                    refine ⟨3032972758707957325035629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2021981839138638216690419 3032972758707957325035629)
                    ·
                      refine ⟨1137364784515483996888361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3032972758707957325035629 1137364784515483996888361)
                      ·
                        rfl

theorem cell23_2215010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_2215010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215010 prefixEnd_2215010 := by exact prefixLift 2215010
  have htrace : WordTrace (prefixWord ++ tailWord_2215010) baseStart_2215010 baseEnd_2215010 := by
    simpa [prefixWord, tailWord_2215010, baseEnd_2215010] using wordTrace_append hprefix tailTrace_2215010
  have hstable : (prefixWord ++ tailWord_2215010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215010).length < 2 ^ (prefixWord ++ tailWord_2215010).sum := by decide
  have hdescent : baseEnd_2215010 < baseStart_2215010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215012 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 5, 2, 4]
def baseStart_2215012 : Nat := 118140960795 + 2215012 * 2 ^ 59
def prefixEnd_2215012 : Nat := 4983230072969 + 3 ^ 40 * 2215012 * 2
def baseEnd_2215012 : Nat := 1137365811476792989063351

theorem tailTrace_2215012 : CollatzResearch.WordTrace tailWord_2215012 prefixEnd_2215012 1137365811476792989063351 := by
  unfold tailWord_2215012
  simp only [CollatzResearch.WordTrace]
  refine ⟨40394062325698646388595645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53858749767598195184794193 40394062325698646388595645)
  ·
    refine ⟨15147773372136992395723367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40394062325698646388595645 15147773372136992395723367)
    ·
      refine ⟨22721660058205488593585051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15147773372136992395723367 22721660058205488593585051)
      ·
        refine ⟨34082490087308232890377577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22721660058205488593585051 34082490087308232890377577)
        ·
          refine ⟨25561867565481174667783183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34082490087308232890377577 25561867565481174667783183)
          ·
            refine ⟨38342801348221762001674775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25561867565481174667783183 38342801348221762001674775)
            ·
              refine ⟨57514202022332643002512163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38342801348221762001674775 57514202022332643002512163)
              ·
                refine ⟨86271303033498964503768245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57514202022332643002512163 86271303033498964503768245)
                ·
                  refine ⟨8087934659390527922228273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 86271303033498964503768245 8087934659390527922228273)
                  ·
                    refine ⟨6065950994542895941671205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8087934659390527922228273 6065950994542895941671205)
                    ·
                      refine ⟨1137365811476792989063351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6065950994542895941671205 1137365811476792989063351)
                      ·
                        rfl

theorem cell23_2215012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_2215012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215012 prefixEnd_2215012 := by exact prefixLift 2215012
  have htrace : WordTrace (prefixWord ++ tailWord_2215012) baseStart_2215012 baseEnd_2215012 := by
    simpa [prefixWord, tailWord_2215012, baseEnd_2215012] using wordTrace_append hprefix tailTrace_2215012
  have hstable : (prefixWord ++ tailWord_2215012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215012).length < 2 ^ (prefixWord ++ tailWord_2215012).sum := by decide
  have hdescent : baseEnd_2215012 < baseStart_2215012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215033 : List Nat := [1, 2, 1, 3, 5, 1, 1, 2, 3, 2, 2]
def baseStart_2215033 : Nat := 118140960795 + 2215033 * 2 ^ 59
def prefixEnd_2215033 : Nat := 4983230072969 + 3 ^ 40 * 2215033 * 2
def baseEnd_2215033 : Nat := 1137376594570537406900755

theorem tailTrace_2215033 : CollatzResearch.WordTrace tailWord_2215033 prefixEnd_2215033 1137376594570537406900755 := by
  unfold tailWord_2215033
  simp only [CollatzResearch.WordTrace]
  refine ⟨80788890584321213363705753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53859260389547475575803835 80788890584321213363705753)
  ·
    refine ⟨60591667938240910022779315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80788890584321213363705753 60591667938240910022779315)
    ·
      refine ⟨90887501907361365034168973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60591667938240910022779315 90887501907361365034168973)
      ·
        refine ⟨34082813215260511887813365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90887501907361365034168973 34082813215260511887813365)
        ·
          refine ⟨3195263738930672989482503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34082813215260511887813365 3195263738930672989482503)
          ·
            refine ⟨4792895608396009484223755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3195263738930672989482503 4792895608396009484223755)
            ·
              refine ⟨7189343412594014226335633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4792895608396009484223755 7189343412594014226335633)
              ·
                refine ⟨5392007559445510669751725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7189343412594014226335633 5392007559445510669751725)
                ·
                  refine ⟨2022002834792066501156897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5392007559445510669751725 2022002834792066501156897)
                  ·
                    refine ⟨1516502126094049875867673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2022002834792066501156897 1516502126094049875867673)
                    ·
                      refine ⟨1137376594570537406900755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1516502126094049875867673 1137376594570537406900755)
                      ·
                        rfl

theorem cell23_2215033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 3, 2, 2].length) (baseStart_2215033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215033 prefixEnd_2215033 := by exact prefixLift 2215033
  have htrace : WordTrace (prefixWord ++ tailWord_2215033) baseStart_2215033 baseEnd_2215033 := by
    simpa [prefixWord, tailWord_2215033, baseEnd_2215033] using wordTrace_append hprefix tailTrace_2215033
  have hstable : (prefixWord ++ tailWord_2215033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215033).length < 2 ^ (prefixWord ++ tailWord_2215033).sum := by decide
  have hdescent : baseEnd_2215033 < baseStart_2215033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215049 : List Nat := [1, 2, 1, 1, 4, 3, 2, 2, 1, 3, 3]
def baseStart_2215049 : Nat := 118140960795 + 2215049 * 2 ^ 59
def prefixEnd_2215049 : Nat := 4983230072969 + 3 ^ 40 * 2215049 * 2
def baseEnd_2215049 : Nat := 1137384810261009344300681

theorem tailTrace_2215049 : CollatzResearch.WordTrace tailWord_2215049 prefixEnd_2215049 1137384810261009344300681 := by
  unfold tailWord_2215049
  simp only [CollatzResearch.WordTrace]
  refine ⟨80789474152263248096288201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53859649434842165397525467 80789474152263248096288201)
  ·
    refine ⟨60592105614197436072216151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80789474152263248096288201 60592105614197436072216151)
    ·
      refine ⟨90888158421296154108324227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60592105614197436072216151 90888158421296154108324227)
      ·
        refine ⟨136332237631944231162486341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90888158421296154108324227 136332237631944231162486341)
        ·
          refine ⟨25562294555989543342966189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 136332237631944231162486341 25562294555989543342966189)
          ·
            refine ⟨9585860458496078753612321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25562294555989543342966189 9585860458496078753612321)
            ·
              refine ⟨7189395343872059065209241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9585860458496078753612321 7189395343872059065209241)
              ·
                refine ⟨5392046507904044298906931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7189395343872059065209241 5392046507904044298906931)
                ·
                  refine ⟨8088069761856066448360397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5392046507904044298906931 8088069761856066448360397)
                  ·
                    refine ⟨3033026160696024918135149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8088069761856066448360397 3033026160696024918135149)
                    ·
                      refine ⟨1137384810261009344300681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3033026160696024918135149 1137384810261009344300681)
                      ·
                        rfl

theorem cell23_2215049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 3, 3].length) (baseStart_2215049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215049 prefixEnd_2215049 := by exact prefixLift 2215049
  have htrace : WordTrace (prefixWord ++ tailWord_2215049) baseStart_2215049 baseEnd_2215049 := by
    simpa [prefixWord, tailWord_2215049, baseEnd_2215049] using wordTrace_append hprefix tailTrace_2215049
  have hstable : (prefixWord ++ tailWord_2215049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215049).length < 2 ^ (prefixWord ++ tailWord_2215049).sum := by decide
  have hdescent : baseEnd_2215049 < baseStart_2215049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215050 : List Nat := [3, 1, 2, 3, 1, 1, 4, 3, 1, 2, 2]
def baseStart_2215050 : Nat := 118140960795 + 2215050 * 2 ^ 59
def prefixEnd_2215050 : Nat := 4983230072969 + 3 ^ 40 * 2215050 * 2
def baseEnd_2215050 : Nat := 1137385323741663840388177

theorem tailTrace_2215050 : CollatzResearch.WordTrace tailWord_2215050 prefixEnd_2215050 1137385323741663840388177 := by
  unfold tailWord_2215050
  simp only [CollatzResearch.WordTrace]
  refine ⟨20197377656314906316768651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53859673750173083511383069 20197377656314906316768651)
  ·
    refine ⟨30296066484472359475152977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20197377656314906316768651 30296066484472359475152977)
    ·
      refine ⟨22722049863354269606364733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30296066484472359475152977 22722049863354269606364733)
      ·
        refine ⟨8520768698757851102386775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22722049863354269606364733 8520768698757851102386775)
        ·
          refine ⟨12781153048136776653580163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8520768698757851102386775 12781153048136776653580163)
          ·
            refine ⟨19171729572205164980370245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12781153048136776653580163 19171729572205164980370245)
            ·
              refine ⟨3594699294788468433819421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19171729572205164980370245 3594699294788468433819421)
              ·
                refine ⟨1348012235545675662682283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3594699294788468433819421 1348012235545675662682283)
                ·
                  refine ⟨2022018353318513494023425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1348012235545675662682283 2022018353318513494023425)
                  ·
                    refine ⟨1516513764988885120517569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2022018353318513494023425 1516513764988885120517569)
                    ·
                      refine ⟨1137385323741663840388177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1516513764988885120517569 1137385323741663840388177)
                      ·
                        rfl

theorem cell23_2215050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_2215050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215050 prefixEnd_2215050 := by exact prefixLift 2215050
  have htrace : WordTrace (prefixWord ++ tailWord_2215050) baseStart_2215050 baseEnd_2215050 := by
    simpa [prefixWord, tailWord_2215050, baseEnd_2215050] using wordTrace_append hprefix tailTrace_2215050
  have hstable : (prefixWord ++ tailWord_2215050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215050).length < 2 ^ (prefixWord ++ tailWord_2215050).sum := by decide
  have hdescent : baseEnd_2215050 < baseStart_2215050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215112 : List Nat := [2, 1, 3, 1, 2, 1, 2, 2, 9]
def baseStart_2215112 : Nat := 118140960795 + 2215112 * 2 ^ 59
def prefixEnd_2215112 : Nat := 4983230072969 + 3 ^ 40 * 2215112 * 2
def baseEnd_2215112 : Nat := 126379684393582510868099

theorem tailTrace_2215112 : CollatzResearch.WordTrace tailWord_2215112 prefixEnd_2215112 126379684393582510868099 := by
  unfold tailWord_2215112
  simp only [CollatzResearch.WordTrace]
  refine ⟨40395885975517504927915795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53861181300690006570554393 40395885975517504927915795)
  ·
    refine ⟨60593828963276257391873693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40395885975517504927915795 60593828963276257391873693)
    ·
      refine ⟨22722685861228596521952635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60593828963276257391873693 22722685861228596521952635)
      ·
        refine ⟨34084028791842894782928953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22722685861228596521952635 34084028791842894782928953)
        ·
          refine ⟨25563021593882171087196715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34084028791842894782928953 25563021593882171087196715)
          ·
            refine ⟨38344532390823256630795073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25563021593882171087196715 38344532390823256630795073)
            ·
              refine ⟨28758399293117442473096305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38344532390823256630795073 28758399293117442473096305)
              ·
                refine ⟨21568799469838081854822229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28758399293117442473096305 21568799469838081854822229)
                ·
                  refine ⟨126379684393582510868099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 21568799469838081854822229 126379684393582510868099)
                  ·
                    rfl

theorem cell23_2215112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 9].length) (baseStart_2215112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215112 prefixEnd_2215112 := by exact prefixLift 2215112
  have htrace : WordTrace (prefixWord ++ tailWord_2215112) baseStart_2215112 baseEnd_2215112 := by
    simpa [prefixWord, tailWord_2215112, baseEnd_2215112] using wordTrace_append hprefix tailTrace_2215112
  have hstable : (prefixWord ++ tailWord_2215112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215112).length < 2 ^ (prefixWord ++ tailWord_2215112).sum := by decide
  have hdescent : baseEnd_2215112 < baseStart_2215112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215140 : List Nat := [2, 3, 1, 1, 1, 2, 6, 1, 2, 2, 2]
def baseStart_2215140 : Nat := 118140960795 + 2215140 * 2 ^ 59
def prefixEnd_2215140 : Nat := 4983230072969 + 3 ^ 40 * 2215140 * 2
def baseEnd_2215140 : Nat := 1137431537000568488262763

theorem tailTrace_2215140 : CollatzResearch.WordTrace tailWord_2215140 prefixEnd_2215140 1137431537000568488262763 := by
  unfold tailWord_2215140
  simp only [CollatzResearch.WordTrace]
  refine ⟨40396396597466785318925437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53861862129955713758567249 40396396597466785318925437)
  ·
    refine ⟨15148648724050044494597039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40396396597466785318925437 15148648724050044494597039)
    ·
      refine ⟨22722973086075066741895559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15148648724050044494597039 22722973086075066741895559)
      ·
        refine ⟨34084459629112600112843339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22722973086075066741895559 34084459629112600112843339)
        ·
          refine ⟨51126689443668900169265009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34084459629112600112843339 51126689443668900169265009)
          ·
            refine ⟨38345017082751675126948757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51126689443668900169265009 38345017082751675126948757)
            ·
              refine ⟨1797422675753984771575723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38345017082751675126948757 1797422675753984771575723)
              ·
                refine ⟨2696134013630977157363585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1797422675753984771575723 2696134013630977157363585)
                ·
                  refine ⟨2022100510223232868022689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2696134013630977157363585 2022100510223232868022689)
                  ·
                    refine ⟨1516575382667424651017017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2022100510223232868022689 1516575382667424651017017)
                    ·
                      refine ⟨1137431537000568488262763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1516575382667424651017017 1137431537000568488262763)
                      ·
                        rfl

theorem cell23_2215140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 1, 2, 2, 2].length) (baseStart_2215140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215140 prefixEnd_2215140 := by exact prefixLift 2215140
  have htrace : WordTrace (prefixWord ++ tailWord_2215140) baseStart_2215140 baseEnd_2215140 := by
    simpa [prefixWord, tailWord_2215140, baseEnd_2215140] using wordTrace_append hprefix tailTrace_2215140
  have hstable : (prefixWord ++ tailWord_2215140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215140).length < 2 ^ (prefixWord ++ tailWord_2215140).sum := by decide
  have hdescent : baseEnd_2215140 < baseStart_2215140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215169 : List Nat := [1, 2, 4, 1, 1, 3, 1, 2, 1, 2, 5]
def baseStart_2215169 : Nat := 118140960795 + 2215169 * 2 ^ 59
def prefixEnd_2215169 : Nat := 4983230072969 + 3 ^ 40 * 2215169 * 2
def baseEnd_2215169 : Nat := 1137446427939548874800129

theorem tailTrace_2215169 : CollatzResearch.WordTrace tailWord_2215169 prefixEnd_2215169 1137446427939548874800129 := by
  unfold tailWord_2215169
  simp only [CollatzResearch.WordTrace]
  refine ⟨80793850911828508590656561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53862567274552339060437707 80793850911828508590656561)
  ·
    refine ⟨60595388183871381442992421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80793850911828508590656561 60595388183871381442992421)
    ·
      refine ⟨11361635284475884020561079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60595388183871381442992421 11361635284475884020561079)
      ·
        refine ⟨17042452926713826030841619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11361635284475884020561079 17042452926713826030841619)
        ·
          refine ⟨25563679390070739046262429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17042452926713826030841619 25563679390070739046262429)
          ·
            refine ⟨9586379771276527142348411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25563679390070739046262429 9586379771276527142348411)
            ·
              refine ⟨14379569656914790713522617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9586379771276527142348411 14379569656914790713522617)
              ·
                refine ⟨10784677242686093035141963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14379569656914790713522617 10784677242686093035141963)
                ·
                  refine ⟨16177015864029139552712945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10784677242686093035141963 16177015864029139552712945)
                  ·
                    refine ⟨12132761898021854664534709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16177015864029139552712945 12132761898021854664534709)
                    ·
                      refine ⟨1137446427939548874800129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12132761898021854664534709 1137446427939548874800129)
                      ·
                        rfl

theorem cell23_2215169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_2215169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215169 prefixEnd_2215169 := by exact prefixLift 2215169
  have htrace : WordTrace (prefixWord ++ tailWord_2215169) baseStart_2215169 baseEnd_2215169 := by
    simpa [prefixWord, tailWord_2215169, baseEnd_2215169] using wordTrace_append hprefix tailTrace_2215169
  have hstable : (prefixWord ++ tailWord_2215169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215169).length < 2 ^ (prefixWord ++ tailWord_2215169).sum := by decide
  have hdescent : baseEnd_2215169 < baseStart_2215169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215196 : List Nat := [2, 2, 3, 1, 1, 1, 3, 1, 1, 6, 2]
def baseStart_2215196 : Nat := 118140960795 + 2215196 * 2 ^ 59
def prefixEnd_2215196 : Nat := 4983230072969 + 3 ^ 40 * 2215196 * 2
def baseEnd_2215196 : Nat := 1137460291917220269162505

theorem tailTrace_2215196 : CollatzResearch.WordTrace tailWord_2215196 prefixEnd_2215196 1137460291917220269162505 := by
  unfold tailWord_2215196
  simp only [CollatzResearch.WordTrace]
  refine ⟨40397417841365346100944721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53863223788487128134592961 40397417841365346100944721)
  ·
    refine ⟨30298063381024009575708541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40397417841365346100944721 30298063381024009575708541)
    ·
      refine ⟨11361773767884003590890703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30298063381024009575708541 11361773767884003590890703)
      ·
        refine ⟨17042660651826005386336055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11361773767884003590890703 17042660651826005386336055)
        ·
          refine ⟨25563990977739008079504083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17042660651826005386336055 25563990977739008079504083)
          ·
            refine ⟨38345986466608512119256125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25563990977739008079504083 38345986466608512119256125)
            ·
              refine ⟨14379744924978192044721047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38345986466608512119256125 14379744924978192044721047)
              ·
                refine ⟨21569617387467288067081571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14379744924978192044721047 21569617387467288067081571)
                ·
                  refine ⟨32354426081200932100622357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21569617387467288067081571 32354426081200932100622357)
                  ·
                    refine ⟨1516613722556293692216673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 32354426081200932100622357 1516613722556293692216673)
                    ·
                      refine ⟨1137460291917220269162505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1516613722556293692216673 1137460291917220269162505)
                      ·
                        rfl

theorem cell23_2215196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 1, 6, 2].length) (baseStart_2215196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215196 prefixEnd_2215196 := by exact prefixLift 2215196
  have htrace : WordTrace (prefixWord ++ tailWord_2215196) baseStart_2215196 baseEnd_2215196 := by
    simpa [prefixWord, tailWord_2215196, baseEnd_2215196] using wordTrace_append hprefix tailTrace_2215196
  have hstable : (prefixWord ++ tailWord_2215196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215196).length < 2 ^ (prefixWord ++ tailWord_2215196).sum := by decide
  have hdescent : baseEnd_2215196 < baseStart_2215196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215213 : List Nat := [1, 5, 3, 1, 1, 2, 1, 1, 1, 3, 4]
def baseStart_2215213 : Nat := 118140960795 + 2215213 * 2 ^ 59
def prefixEnd_2215213 : Nat := 4983230072969 + 3 ^ 40 * 2215213 * 2
def baseEnd_2215213 : Nat := 1137469021088346702649927

theorem tailTrace_2215213 : CollatzResearch.WordTrace tailWord_2215213 prefixEnd_2215213 1137469021088346702649927 := by
  unfold tailWord_2215213
  simp only [CollatzResearch.WordTrace]
  refine ⟨80795455723669104105258293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53863637149112736070172195 80795455723669104105258293)
  ·
    refine ⟨7574573974093978509867965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80795455723669104105258293 7574573974093978509867965)
    ·
      refine ⟨2840465240285241941200487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7574573974093978509867965 2840465240285241941200487)
      ·
        refine ⟨4260697860427862911800731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2840465240285241941200487 4260697860427862911800731)
        ·
          refine ⟨6391046790641794367701097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4260697860427862911800731 6391046790641794367701097)
          ·
            refine ⟨4793285092981345775775823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6391046790641794367701097 4793285092981345775775823)
            ·
              refine ⟨7189927639472018663663735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4793285092981345775775823 7189927639472018663663735)
              ·
                refine ⟨10784891459208027995495603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7189927639472018663663735 10784891459208027995495603)
                ·
                  refine ⟨16177337188812041993243405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10784891459208027995495603 16177337188812041993243405)
                  ·
                    refine ⟨6066501445804515747466277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16177337188812041993243405 6066501445804515747466277)
                    ·
                      refine ⟨1137469021088346702649927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6066501445804515747466277 1137469021088346702649927)
                      ·
                        rfl

theorem cell23_2215213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_2215213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215213 prefixEnd_2215213 := by exact prefixLift 2215213
  have htrace : WordTrace (prefixWord ++ tailWord_2215213) baseStart_2215213 baseEnd_2215213 := by
    simpa [prefixWord, tailWord_2215213, baseEnd_2215213] using wordTrace_append hprefix tailTrace_2215213
  have hstable : (prefixWord ++ tailWord_2215213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215213).length < 2 ^ (prefixWord ++ tailWord_2215213).sum := by decide
  have hdescent : baseEnd_2215213 < baseStart_2215213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215239 : List Nat := [1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 6]
def baseStart_2215239 : Nat := 118140960795 + 2215239 * 2 ^ 59
def prefixEnd_2215239 : Nat := 4983230072969 + 3 ^ 40 * 2215239 * 2
def baseEnd_2215239 : Nat := 1137482371585363600924807

theorem tailTrace_2215239 : CollatzResearch.WordTrace tailWord_2215239 prefixEnd_2215239 1137482371585363600924807 := by
  unfold tailWord_2215239
  simp only [CollatzResearch.WordTrace]
  refine ⟨80796404021574910545704771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53864269347716607030469847 80796404021574910545704771)
  ·
    refine ⟨121194606032362365818557157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80796404021574910545704771 121194606032362365818557157)
    ·
      refine ⟨22723988631067943590979467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121194606032362365818557157 22723988631067943590979467)
      ·
        refine ⟨34085982946601915386469201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22723988631067943590979467 34085982946601915386469201)
        ·
          refine ⟨25564487209951436539851901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34085982946601915386469201 25564487209951436539851901)
          ·
            refine ⟨9586682703731788702444463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25564487209951436539851901 9586682703731788702444463)
            ·
              refine ⟨14380024055597683053666695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9586682703731788702444463 14380024055597683053666695)
              ·
                refine ⟨21570036083396524580500043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14380024055597683053666695 21570036083396524580500043)
                ·
                  refine ⟨32355054125094786870750065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21570036083396524580500043 32355054125094786870750065)
                  ·
                    refine ⟨24266290593821090153062549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32355054125094786870750065 24266290593821090153062549)
                    ·
                      refine ⟨1137482371585363600924807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24266290593821090153062549 1137482371585363600924807)
                      ·
                        rfl

theorem cell23_2215239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_2215239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215239 prefixEnd_2215239 := by exact prefixLift 2215239
  have htrace : WordTrace (prefixWord ++ tailWord_2215239) baseStart_2215239 baseEnd_2215239 := by
    simpa [prefixWord, tailWord_2215239, baseEnd_2215239] using wordTrace_append hprefix tailTrace_2215239
  have hstable : (prefixWord ++ tailWord_2215239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215239).length < 2 ^ (prefixWord ++ tailWord_2215239).sum := by decide
  have hdescent : baseEnd_2215239 < baseStart_2215239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215253 : List Nat := [1, 3, 2, 2, 3, 2, 3, 1, 6]
def baseStart_2215253 : Nat := 118140960795 + 2215253 * 2 ^ 59
def prefixEnd_2215253 : Nat := 4983230072969 + 3 ^ 40 * 2215253 * 2
def baseEnd_2215253 : Nat := 126387728923836282905527

theorem tailTrace_2215253 : CollatzResearch.WordTrace tailWord_2215253 prefixEnd_2215253 126387728923836282905527 := by
  unfold tailWord_2215253
  simp only [CollatzResearch.WordTrace]
  refine ⟨80796914643524190936714413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53864609762349460624476275 80796914643524190936714413)
  ·
    refine ⟨30298842991321571601267905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80796914643524190936714413 30298842991321571601267905)
    ·
      refine ⟨22724132243491178700950929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30298842991321571601267905 22724132243491178700950929)
      ·
        refine ⟨17043099182618384025713197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22724132243491178700950929 17043099182618384025713197)
        ·
          refine ⟨6391162193481894009642449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17043099182618384025713197 6391162193481894009642449)
          ·
            refine ⟨4793371645111420507231837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6391162193481894009642449 4793371645111420507231837)
            ·
              refine ⟨1797514366916782690211939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4793371645111420507231837 1797514366916782690211939)
              ·
                refine ⟨2696271550375174035317909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1797514366916782690211939 2696271550375174035317909)
                ·
                  refine ⟨126387728923836282905527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2696271550375174035317909 126387728923836282905527)
                  ·
                    rfl

theorem cell23_2215253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 1, 6].length) (baseStart_2215253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215253 prefixEnd_2215253 := by exact prefixLift 2215253
  have htrace : WordTrace (prefixWord ++ tailWord_2215253) baseStart_2215253 baseEnd_2215253 := by
    simpa [prefixWord, tailWord_2215253, baseEnd_2215253] using wordTrace_append hprefix tailTrace_2215253
  have hstable : (prefixWord ++ tailWord_2215253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215253).length < 2 ^ (prefixWord ++ tailWord_2215253).sum := by decide
  have hdescent : baseEnd_2215253 < baseStart_2215253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215256 : List Nat := [2, 1, 2, 2, 1, 1, 3, 1, 3, 5, 2]
def baseStart_2215256 : Nat := 118140960795 + 2215256 * 2 ^ 59
def prefixEnd_2215256 : Nat := 4983230072969 + 3 ^ 40 * 2215256 * 2
def baseEnd_2215256 : Nat := 1137491100756490034412229

theorem tailTrace_2215256 : CollatzResearch.WordTrace tailWord_2215256 prefixEnd_2215256 1137491100756490034412229 := by
  unfold tailWord_2215256
  simp only [CollatzResearch.WordTrace]
  refine ⟨40398512031256661224536811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53864682708342214966049081 40398512031256661224536811)
  ·
    refine ⟨60597768046884991836805217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40398512031256661224536811 60597768046884991836805217)
    ·
      refine ⟨45448326035163743877603913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60597768046884991836805217 45448326035163743877603913)
      ·
        refine ⟨34086244526372807908202935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45448326035163743877603913 34086244526372807908202935)
        ·
          refine ⟨51129366789559211862304403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34086244526372807908202935 51129366789559211862304403)
          ·
            refine ⟨76694050184338817793456605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51129366789559211862304403 76694050184338817793456605)
            ·
              refine ⟨28760268819127056672546227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76694050184338817793456605 28760268819127056672546227)
              ·
                refine ⟨43140403228690585008819341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28760268819127056672546227 43140403228690585008819341)
                ·
                  refine ⟨16177651210758969378307253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43140403228690585008819341 16177651210758969378307253)
                  ·
                    refine ⟨1516654801008653379216305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16177651210758969378307253 1516654801008653379216305)
                    ·
                      refine ⟨1137491100756490034412229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1516654801008653379216305 1137491100756490034412229)
                      ·
                        rfl

theorem cell23_2215256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 3, 5, 2].length) (baseStart_2215256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215256 prefixEnd_2215256 := by exact prefixLift 2215256
  have htrace : WordTrace (prefixWord ++ tailWord_2215256) baseStart_2215256 baseEnd_2215256 := by
    simpa [prefixWord, tailWord_2215256, baseEnd_2215256] using wordTrace_append hprefix tailTrace_2215256
  have hstable : (prefixWord ++ tailWord_2215256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215256).length < 2 ^ (prefixWord ++ tailWord_2215256).sum := by decide
  have hdescent : baseEnd_2215256 < baseStart_2215256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215274 : List Nat := [3, 1, 3, 3, 3, 1, 1, 3, 1, 4]
def baseStart_2215274 : Nat := 118140960795 + 2215274 * 2 ^ 59
def prefixEnd_2215274 : Nat := 4983230072969 + 3 ^ 40 * 2215274 * 2
def baseEnd_2215274 : Nat := 379166781136090321329049

theorem tailTrace_2215274 : CollatzResearch.WordTrace tailWord_2215274 prefixEnd_2215274 379166781136090321329049 := by
  unfold tailWord_2215274
  simp only [CollatzResearch.WordTrace]
  refine ⟨20199420144112027880807219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53865120384298741015485917 20199420144112027880807219)
  ·
    refine ⟨30299130216168041821210829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20199420144112027880807219 30299130216168041821210829)
    ·
      refine ⟨11362173831063015682954061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30299130216168041821210829 11362173831063015682954061)
      ·
        refine ⟨4260815186648630881107773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11362173831063015682954061 4260815186648630881107773)
        ·
          refine ⟨1597805694993236580415415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4260815186648630881107773 1597805694993236580415415)
          ·
            refine ⟨2396708542489854870623123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1597805694993236580415415 2396708542489854870623123)
            ·
              refine ⟨3595062813734782305934685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2396708542489854870623123 3595062813734782305934685)
              ·
                refine ⟨1348148555150543364725507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3595062813734782305934685 1348148555150543364725507)
                ·
                  refine ⟨2022222832725815047088261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1348148555150543364725507 2022222832725815047088261)
                  ·
                    refine ⟨379166781136090321329049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2022222832725815047088261 379166781136090321329049)
                    ·
                      rfl

theorem cell23_2215274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_2215274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215274 prefixEnd_2215274 := by exact prefixLift 2215274
  have htrace : WordTrace (prefixWord ++ tailWord_2215274) baseStart_2215274 baseEnd_2215274 := by
    simpa [prefixWord, tailWord_2215274, baseEnd_2215274] using wordTrace_append hprefix tailTrace_2215274
  have hstable : (prefixWord ++ tailWord_2215274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215274).length < 2 ^ (prefixWord ++ tailWord_2215274).sum := by decide
  have hdescent : baseEnd_2215274 < baseStart_2215274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215279 : List Nat := [1, 1, 2, 1, 3, 1, 4, 1, 3, 6]
def baseStart_2215279 : Nat := 118140960795 + 2215279 * 2 ^ 59
def prefixEnd_2215279 : Nat := 4983230072969 + 3 ^ 40 * 2215279 * 2
def baseEnd_2215279 : Nat := 379167636937181148141541

theorem tailTrace_2215279 : CollatzResearch.WordTrace tailWord_2215279 prefixEnd_2215279 379167636937181148141541 := by
  unfold tailWord_2215279
  simp only [CollatzResearch.WordTrace]
  refine ⟨80797862941429997377160891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53865241960953331584773927 80797862941429997377160891)
  ·
    refine ⟨121196794412144996065741337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80797862941429997377160891 121196794412144996065741337)
    ·
      refine ⟨90897595809108747049306003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121196794412144996065741337 90897595809108747049306003)
      ·
        refine ⟨136346393713663120573959005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90897595809108747049306003 136346393713663120573959005)
        ·
          refine ⟨51129897642623670215234627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136346393713663120573959005 51129897642623670215234627)
          ·
            refine ⟨76694846463935505322851941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51129897642623670215234627 76694846463935505322851941)
            ·
              refine ⟨14380283711987907248034739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76694846463935505322851941 14380283711987907248034739)
              ·
                refine ⟨21570425567981860872052109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14380283711987907248034739 21570425567981860872052109)
                ·
                  refine ⟨8088909587993197827019541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21570425567981860872052109 8088909587993197827019541)
                  ·
                    refine ⟨379167636937181148141541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8088909587993197827019541 379167636937181148141541)
                    ·
                      rfl

theorem cell23_2215279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 6].length) (baseStart_2215279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215279 prefixEnd_2215279 := by exact prefixLift 2215279
  have htrace : WordTrace (prefixWord ++ tailWord_2215279) baseStart_2215279 baseEnd_2215279 := by
    simpa [prefixWord, tailWord_2215279, baseEnd_2215279] using wordTrace_append hprefix tailTrace_2215279
  have hstable : (prefixWord ++ tailWord_2215279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215279).length < 2 ^ (prefixWord ++ tailWord_2215279).sum := by decide
  have hdescent : baseEnd_2215279 < baseStart_2215279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215297 : List Nat := [1, 2, 4, 3, 2, 2, 1, 1, 3, 1, 3]
def baseStart_2215297 : Nat := 118140960795 + 2215297 * 2 ^ 59
def prefixEnd_2215297 : Nat := 4983230072969 + 3 ^ 40 * 2215297 * 2
def baseEnd_2215297 : Nat := 1137512153463324373999541

theorem tailTrace_2215297 : CollatzResearch.WordTrace tailWord_2215297 prefixEnd_2215297 1137512153463324373999541 := by
  unfold tailWord_2215297
  simp only [CollatzResearch.WordTrace]
  refine ⟨80798519455364786451316145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53865679636909857634210763 80798519455364786451316145)
  ·
    refine ⟨60598889591523589838487109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80798519455364786451316145 60598889591523589838487109)
    ·
      refine ⟨11362291798410673094716333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60598889591523589838487109 11362291798410673094716333)
      ·
        refine ⟨4260859424404002410518625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11362291798410673094716333 4260859424404002410518625)
        ·
          refine ⟨3195644568303001807888969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4260859424404002410518625 3195644568303001807888969)
          ·
            refine ⟨2396733426227251355916727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3195644568303001807888969 2396733426227251355916727)
            ·
              refine ⟨3595100139340877033875091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2396733426227251355916727 3595100139340877033875091)
              ·
                refine ⟨5392650209011315550812637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3595100139340877033875091 5392650209011315550812637)
                ·
                  refine ⟨2022243828379243331554739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5392650209011315550812637 2022243828379243331554739)
                  ·
                    refine ⟨3033365742568864997332109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2022243828379243331554739 3033365742568864997332109)
                    ·
                      refine ⟨1137512153463324373999541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3033365742568864997332109 1137512153463324373999541)
                      ·
                        rfl

theorem cell23_2215297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_2215297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215297 prefixEnd_2215297 := by exact prefixLift 2215297
  have htrace : WordTrace (prefixWord ++ tailWord_2215297) baseStart_2215297 baseEnd_2215297 := by
    simpa [prefixWord, tailWord_2215297, baseEnd_2215297] using wordTrace_append hprefix tailTrace_2215297
  have hstable : (prefixWord ++ tailWord_2215297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215297).length < 2 ^ (prefixWord ++ tailWord_2215297).sum := by decide
  have hdescent : baseEnd_2215297 < baseStart_2215297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215363 : List Nat := [1, 1, 1, 3, 1, 1, 5, 2, 3, 3, 2]
def baseStart_2215363 : Nat := 118140960795 + 2215363 * 2 ^ 59
def prefixEnd_2215363 : Nat := 4983230072969 + 3 ^ 40 * 2215363 * 2
def baseEnd_2215363 : Nat := 1137546043186521115774237

theorem tailTrace_2215363 : CollatzResearch.WordTrace tailWord_2215363 prefixEnd_2215363 1137546043186521115774237 := by
  unfold tailWord_2215363
  simp only [CollatzResearch.WordTrace]
  refine ⟨80800926673125679723218743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53867284448750453148812495 80800926673125679723218743)
  ·
    refine ⟨121201390009688519584828115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80800926673125679723218743 121201390009688519584828115)
    ·
      refine ⟨181802085014532779377242173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121201390009688519584828115 181802085014532779377242173)
      ·
        refine ⟨68175781880449792266465815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 181802085014532779377242173 68175781880449792266465815)
        ·
          refine ⟨102263672820674688399698723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68175781880449792266465815 102263672820674688399698723)
          ·
            refine ⟨153395509231012032599548085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102263672820674688399698723 153395509231012032599548085)
            ·
              refine ⟨14380828990407378056207633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 153395509231012032599548085 14380828990407378056207633)
              ·
                refine ⟨10785621742805533542155725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14380828990407378056207633 10785621742805533542155725)
                ·
                  refine ⟨4044608153552075078308397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10785621742805533542155725 4044608153552075078308397)
                  ·
                    refine ⟨1516728057582028154365649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4044608153552075078308397 1516728057582028154365649)
                    ·
                      refine ⟨1137546043186521115774237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1516728057582028154365649 1137546043186521115774237)
                      ·
                        rfl

theorem cell23_2215363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 3, 3, 2].length) (baseStart_2215363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215363 prefixEnd_2215363 := by exact prefixLift 2215363
  have htrace : WordTrace (prefixWord ++ tailWord_2215363) baseStart_2215363 baseEnd_2215363 := by
    simpa [prefixWord, tailWord_2215363, baseEnd_2215363] using wordTrace_append hprefix tailTrace_2215363
  have hstable : (prefixWord ++ tailWord_2215363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215363).length < 2 ^ (prefixWord ++ tailWord_2215363).sum := by decide
  have hdescent : baseEnd_2215363 < baseStart_2215363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215370 : List Nat := [3, 1, 2, 1, 2, 3, 2, 3, 2, 1, 3]
def baseStart_2215370 : Nat := 118140960795 + 2215370 * 2 ^ 59
def prefixEnd_2215370 : Nat := 4983230072969 + 3 ^ 40 * 2215370 * 2
def baseEnd_2215370 : Nat := 1137549637551102588386705

theorem tailTrace_2215370 : CollatzResearch.WordTrace tailWord_2215370 prefixEnd_2215370 1137549637551102588386705 := by
  unfold tailWord_2215370
  simp only [CollatzResearch.WordTrace]
  refine ⟨20200295496025079979680891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53867454656066879945815709 20200295496025079979680891)
  ·
    refine ⟨30300443244037619969521337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20200295496025079979680891 30300443244037619969521337)
    ·
      refine ⟨22725332433028214977141003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30300443244037619969521337 22725332433028214977141003)
      ·
        refine ⟨34087998649542322465711505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22725332433028214977141003 34087998649542322465711505)
        ·
          refine ⟨25565998987156741849283629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34087998649542322465711505 25565998987156741849283629)
          ·
            refine ⟨9587249620183778193481361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25565998987156741849283629 9587249620183778193481361)
            ·
              refine ⟨7190437215137833645111021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9587249620183778193481361 7190437215137833645111021)
              ·
                refine ⟨2696413955676687616916633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7190437215137833645111021 2696413955676687616916633)
                ·
                  refine ⟨2022310466757515712687475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2696413955676687616916633 2022310466757515712687475)
                  ·
                    refine ⟨3033465700136273569031213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2022310466757515712687475 3033465700136273569031213)
                    ·
                      refine ⟨1137549637551102588386705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3033465700136273569031213 1137549637551102588386705)
                      ·
                        rfl

theorem cell23_2215370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 3, 2, 1, 3].length) (baseStart_2215370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215370 prefixEnd_2215370 := by exact prefixLift 2215370
  have htrace : WordTrace (prefixWord ++ tailWord_2215370) baseStart_2215370 baseEnd_2215370 := by
    simpa [prefixWord, tailWord_2215370, baseEnd_2215370] using wordTrace_append hprefix tailTrace_2215370
  have hstable : (prefixWord ++ tailWord_2215370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215370).length < 2 ^ (prefixWord ++ tailWord_2215370).sum := by decide
  have hdescent : baseEnd_2215370 < baseStart_2215370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215396 : List Nat := [2, 3, 1, 1, 1, 1, 1, 5, 2, 1, 5]
def baseStart_2215396 : Nat := 118140960795 + 2215396 * 2 ^ 59
def prefixEnd_2215396 : Nat := 4983230072969 + 3 ^ 40 * 2215396 * 2
def baseEnd_2215396 : Nat := 1137562988048119486661585

theorem tailTrace_2215396 : CollatzResearch.WordTrace tailWord_2215396 prefixEnd_2215396 1137562988048119486661585 := by
  unfold tailWord_2215396
  simp only [CollatzResearch.WordTrace]
  refine ⟨40401065141003063179585021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53868086854670750906113361 40401065141003063179585021)
  ·
    refine ⟨15150399427876148692344383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40401065141003063179585021 15150399427876148692344383)
    ·
      refine ⟨22725599141814223038516575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15150399427876148692344383 22725599141814223038516575)
      ·
        refine ⟨34088398712721334557774863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22725599141814223038516575 34088398712721334557774863)
        ·
          refine ⟨51132598069082001836662295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34088398712721334557774863 51132598069082001836662295)
          ·
            refine ⟨76698897103623002754993443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51132598069082001836662295 76698897103623002754993443)
            ·
              refine ⟨115048345655434504132490165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76698897103623002754993443 115048345655434504132490165)
              ·
                refine ⟨10785782405196984762420953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 115048345655434504132490165 10785782405196984762420953)
                ·
                  refine ⟨8089336803897738571815715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10785782405196984762420953 8089336803897738571815715)
                  ·
                    refine ⟨12134005205846607857723573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8089336803897738571815715 12134005205846607857723573)
                    ·
                      refine ⟨1137562988048119486661585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12134005205846607857723573 1137562988048119486661585)
                      ·
                        rfl

theorem cell23_2215396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_2215396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215396 prefixEnd_2215396 := by exact prefixLift 2215396
  have htrace : WordTrace (prefixWord ++ tailWord_2215396) baseStart_2215396 baseEnd_2215396 := by
    simpa [prefixWord, tailWord_2215396, baseEnd_2215396] using wordTrace_append hprefix tailTrace_2215396
  have hstable : (prefixWord ++ tailWord_2215396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215396).length < 2 ^ (prefixWord ++ tailWord_2215396).sum := by decide
  have hdescent : baseEnd_2215396 < baseStart_2215396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215397 : List Nat := [1, 3, 1, 5, 1, 2, 1, 3, 1, 3, 2]
def baseStart_2215397 : Nat := 118140960795 + 2215397 * 2 ^ 59
def prefixEnd_2215397 : Nat := 4983230072969 + 3 ^ 40 * 2215397 * 2
def baseEnd_2215397 : Nat := 1137563501528773982749081

theorem tailTrace_2215397 : CollatzResearch.WordTrace tailWord_2215397 prefixEnd_2215397 1137563501528773982749081 := by
  unfold tailWord_2215397
  simp only [CollatzResearch.WordTrace]
  refine ⟨80802166755002503529956445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53868111170001669019970963 80802166755002503529956445)
  ·
    refine ⟨30300812533125938823733667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80802166755002503529956445 30300812533125938823733667)
    ·
      refine ⟨45451218799688908235600501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30300812533125938823733667 45451218799688908235600501)
      ·
        refine ⟨4261051762470835147087547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45451218799688908235600501 4261051762470835147087547)
        ·
          refine ⟨6391577643706252720631321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4261051762470835147087547 6391577643706252720631321)
          ·
            refine ⟨4793683232779689540473491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6391577643706252720631321 4793683232779689540473491)
            ·
              refine ⟨7190524849169534310710237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4793683232779689540473491 7190524849169534310710237)
              ·
                refine ⟨2696446818438575366516339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7190524849169534310710237 2696446818438575366516339)
                ·
                  refine ⟨4044670227657863049774509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2696446818438575366516339 4044670227657863049774509)
                  ·
                    refine ⟨1516751335371698643665441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4044670227657863049774509 1516751335371698643665441)
                    ·
                      refine ⟨1137563501528773982749081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1516751335371698643665441 1137563501528773982749081)
                      ·
                        rfl

theorem cell23_2215397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_2215397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215397 prefixEnd_2215397 := by exact prefixLift 2215397
  have htrace : WordTrace (prefixWord ++ tailWord_2215397) baseStart_2215397 baseEnd_2215397 := by
    simpa [prefixWord, tailWord_2215397, baseEnd_2215397] using wordTrace_append hprefix tailTrace_2215397
  have hstable : (prefixWord ++ tailWord_2215397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215397).length < 2 ^ (prefixWord ++ tailWord_2215397).sum := by decide
  have hdescent : baseEnd_2215397 < baseStart_2215397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215416 : List Nat := [2, 1, 2, 1, 1, 5, 1, 3, 7]
def baseStart_2215416 : Nat := 118140960795 + 2215416 * 2 ^ 59
def prefixEnd_2215416 : Nat := 4983230072969 + 3 ^ 40 * 2215416 * 2
def baseEnd_2215416 : Nat := 126397028629023267601277

theorem tailTrace_2215416 : CollatzResearch.WordTrace tailWord_2215416 prefixEnd_2215416 126397028629023267601277 := by
  unfold tailWord_2215416
  simp only [CollatzResearch.WordTrace]
  refine ⟨40401429870966834887449051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53868573161289113183265401 40401429870966834887449051)
  ·
    refine ⟨60602144806450252331173577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40401429870966834887449051 60602144806450252331173577)
    ·
      refine ⟨45451608604837689248380183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60602144806450252331173577 45451608604837689248380183)
      ·
        refine ⟨68177412907256533872570275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45451608604837689248380183 68177412907256533872570275)
        ·
          refine ⟨102266119360884800808855413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68177412907256533872570275 102266119360884800808855413)
          ·
            refine ⟨9587448690082950075830195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 102266119360884800808855413 9587448690082950075830195)
            ·
              refine ⟨14381173035124425113745293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9587448690082950075830195 14381173035124425113745293)
              ·
                refine ⟨5392939888171659417654485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14381173035124425113745293 5392939888171659417654485)
                ·
                  refine ⟨126397028629023267601277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5392939888171659417654485 126397028629023267601277)
                  ·
                    rfl

theorem cell23_2215416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 7].length) (baseStart_2215416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215416 prefixEnd_2215416 := by exact prefixLift 2215416
  have htrace : WordTrace (prefixWord ++ tailWord_2215416) baseStart_2215416 baseEnd_2215416 := by
    simpa [prefixWord, tailWord_2215416, baseEnd_2215416] using wordTrace_append hprefix tailTrace_2215416
  have hstable : (prefixWord ++ tailWord_2215416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215416).length < 2 ^ (prefixWord ++ tailWord_2215416).sum := by decide
  have hdescent : baseEnd_2215416 < baseStart_2215416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215478 : List Nat := [5, 1, 2, 1, 3, 2, 2, 1, 2, 2, 2]
def baseStart_2215478 : Nat := 118140960795 + 2215478 * 2 ^ 59
def prefixEnd_2215478 : Nat := 4983230072969 + 3 ^ 40 * 2215478 * 2
def baseEnd_2215478 : Nat := 1137605093461788165836209

theorem tailTrace_2215478 : CollatzResearch.WordTrace tailWord_2215478 prefixEnd_2215478 1137605093461788165836209 := by
  unfold tailWord_2215478
  simp only [CollatzResearch.WordTrace]
  refine ⟨5050320066731815897728443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53870080711806036242436725 5050320066731815897728443)
  ·
    refine ⟨7575480100097723846592665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5050320066731815897728443 7575480100097723846592665)
    ·
      refine ⟨5681610075073292884944499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7575480100097723846592665 5681610075073292884944499)
      ·
        refine ⟨8522415112609939327416749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5681610075073292884944499 8522415112609939327416749)
        ·
          refine ⟨3195905667228727247781281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8522415112609939327416749 3195905667228727247781281)
          ·
            refine ⟨2396929250421545435835961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3195905667228727247781281 2396929250421545435835961)
            ·
              refine ⟨1797696937816159076876971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2396929250421545435835961 1797696937816159076876971)
              ·
                refine ⟨2696545406724238615315457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1797696937816159076876971 2696545406724238615315457)
                ·
                  refine ⟨2022409055043178961486593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2696545406724238615315457 2022409055043178961486593)
                  ·
                    refine ⟨1516806791282384221114945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2022409055043178961486593 1516806791282384221114945)
                    ·
                      refine ⟨1137605093461788165836209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1516806791282384221114945 1137605093461788165836209)
                      ·
                        rfl

theorem cell23_2215478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_2215478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215478 prefixEnd_2215478 := by exact prefixLift 2215478
  have htrace : WordTrace (prefixWord ++ tailWord_2215478) baseStart_2215478 baseEnd_2215478 := by
    simpa [prefixWord, tailWord_2215478, baseEnd_2215478] using wordTrace_append hprefix tailTrace_2215478
  have hstable : (prefixWord ++ tailWord_2215478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215478).length < 2 ^ (prefixWord ++ tailWord_2215478).sum := by decide
  have hdescent : baseEnd_2215478 < baseStart_2215478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215493 : List Nat := [1, 3, 1, 1, 1, 4, 2, 1, 5, 4]
def baseStart_2215493 : Nat := 118140960795 + 2215493 * 2 ^ 59
def prefixEnd_2215493 : Nat := 4983230072969 + 3 ^ 40 * 2215493 * 2
def baseEnd_2215493 : Nat := 379204265223868535716213

theorem tailTrace_2215493 : CollatzResearch.WordTrace tailWord_2215493 prefixEnd_2215493 379204265223868535716213 := by
  unfold tailWord_2215493
  simp only [CollatzResearch.WordTrace]
  refine ⟨80805668162654711925451133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53870445441769807950300755 80805668162654711925451133)
  ·
    refine ⟨30302125560995516972044175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80805668162654711925451133 30302125560995516972044175)
    ·
      refine ⟨45453188341493275458066263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30302125560995516972044175 45453188341493275458066263)
      ·
        refine ⟨68179782512239913187099395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45453188341493275458066263 68179782512239913187099395)
        ·
          refine ⟨102269673768359869780649093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68179782512239913187099395 102269673768359869780649093)
          ·
            refine ⟨19175563831567475583871705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102269673768359869780649093 19175563831567475583871705)
            ·
              refine ⟨14381672873675606687903779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19175563831567475583871705 14381672873675606687903779)
              ·
                refine ⟨21572509310513410031855669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14381672873675606687903779 21572509310513410031855669)
                ·
                  refine ⟨2022422747860632190486469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21572509310513410031855669 2022422747860632190486469)
                  ·
                    refine ⟨379204265223868535716213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2022422747860632190486469 379204265223868535716213)
                    ·
                      rfl

theorem cell23_2215493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 5, 4].length) (baseStart_2215493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215493 prefixEnd_2215493 := by exact prefixLift 2215493
  have htrace : WordTrace (prefixWord ++ tailWord_2215493) baseStart_2215493 baseEnd_2215493 := by
    simpa [prefixWord, tailWord_2215493, baseEnd_2215493] using wordTrace_append hprefix tailTrace_2215493
  have hstable : (prefixWord ++ tailWord_2215493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215493).length < 2 ^ (prefixWord ++ tailWord_2215493).sum := by decide
  have hdescent : baseEnd_2215493 < baseStart_2215493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215496 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 3, 3, 6]
def baseStart_2215496 : Nat := 118140960795 + 2215496 * 2 ^ 59
def prefixEnd_2215496 : Nat := 4983230072969 + 3 ^ 40 * 2215496 * 2
def baseEnd_2215496 : Nat := 1137614336113569095411125

theorem tailTrace_2215496 : CollatzResearch.WordTrace tailWord_2215496 prefixEnd_2215496 1137614336113569095411125 := by
  unfold tailWord_2215496
  simp only [CollatzResearch.WordTrace]
  refine ⟨40402888790821921718905171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53870518387762562291873561 40402888790821921718905171)
  ·
    refine ⟨60604333186232882578357757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40402888790821921718905171 60604333186232882578357757)
    ·
      refine ⟨22726624944837330966884159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60604333186232882578357757 22726624944837330966884159)
      ·
        refine ⟨34089937417255996450326239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22726624944837330966884159 34089937417255996450326239)
        ·
          refine ⟨51134906125883994675489359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34089937417255996450326239 51134906125883994675489359)
          ·
            refine ⟨76702359188825992013234039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51134906125883994675489359 76702359188825992013234039)
            ·
              refine ⟨115053538783238988019851059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76702359188825992013234039 115053538783238988019851059)
              ·
                refine ⟨172580308174858482029776589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115053538783238988019851059 172580308174858482029776589)
                ·
                  refine ⟨64717615565571930761166221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 172580308174858482029776589 64717615565571930761166221)
                  ·
                    refine ⟨24269105837089474035437333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64717615565571930761166221 24269105837089474035437333)
                    ·
                      refine ⟨1137614336113569095411125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24269105837089474035437333 1137614336113569095411125)
                      ·
                        rfl

theorem cell23_2215496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_2215496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215496 prefixEnd_2215496 := by exact prefixLift 2215496
  have htrace : WordTrace (prefixWord ++ tailWord_2215496) baseStart_2215496 baseEnd_2215496 := by
    simpa [prefixWord, tailWord_2215496, baseEnd_2215496] using wordTrace_append hprefix tailTrace_2215496
  have hstable : (prefixWord ++ tailWord_2215496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215496).length < 2 ^ (prefixWord ++ tailWord_2215496).sum := by decide
  have hdescent : baseEnd_2215496 < baseStart_2215496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215500 : List Nat := [2, 2, 1, 3, 1, 4, 2, 1, 2, 1, 4]
def baseStart_2215500 : Nat := 118140960795 + 2215500 * 2 ^ 59
def prefixEnd_2215500 : Nat := 4983230072969 + 3 ^ 40 * 2215500 * 2
def baseEnd_2215500 : Nat := 1137616390036187079761107

theorem tailTrace_2215500 : CollatzResearch.WordTrace tailWord_2215500 prefixEnd_2215500 1137616390036187079761107 := by
  unfold tailWord_2215500
  simp only [CollatzResearch.WordTrace]
  refine ⟨40402961736814676060477977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53870615649086234747303969 40402961736814676060477977)
  ·
    refine ⟨30302221302611007045358483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40402961736814676060477977 30302221302611007045358483)
    ·
      refine ⟨45453331953916510568037725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30302221302611007045358483 45453331953916510568037725)
      ·
        refine ⟨17044999482718691463014147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45453331953916510568037725 17044999482718691463014147)
        ·
          refine ⟨25567499224078037194521221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17044999482718691463014147 25567499224078037194521221)
          ·
            refine ⟨4793906104514631973972729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25567499224078037194521221 4793906104514631973972729)
            ·
              refine ⟨3595429578385973980479547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4793906104514631973972729 3595429578385973980479547)
              ·
                refine ⟨5393144367578960970719321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3595429578385973980479547 5393144367578960970719321)
                ·
                  refine ⟨4044858275684220728039491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5393144367578960970719321 4044858275684220728039491)
                  ·
                    refine ⟨6067287413526331092059237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4044858275684220728039491 6067287413526331092059237)
                    ·
                      refine ⟨1137616390036187079761107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6067287413526331092059237 1137616390036187079761107)
                      ·
                        rfl

theorem cell23_2215500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_2215500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215500 prefixEnd_2215500 := by exact prefixLift 2215500
  have htrace : WordTrace (prefixWord ++ tailWord_2215500) baseStart_2215500 baseEnd_2215500 := by
    simpa [prefixWord, tailWord_2215500, baseEnd_2215500] using wordTrace_append hprefix tailTrace_2215500
  have hstable : (prefixWord ++ tailWord_2215500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215500).length < 2 ^ (prefixWord ++ tailWord_2215500).sum := by decide
  have hdescent : baseEnd_2215500 < baseStart_2215500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215523 : List Nat := [1, 1, 1, 5, 1, 3, 1, 4, 6]
def baseStart_2215523 : Nat := 118140960795 + 2215523 * 2 ^ 59
def prefixEnd_2215523 : Nat := 4983230072969 + 3 ^ 40 * 2215523 * 2
def baseEnd_2215523 : Nat := 126403133343471165530389

theorem tailTrace_2215523 : CollatzResearch.WordTrace tailWord_2215523 prefixEnd_2215523 126403133343471165530389 := by
  unfold tailWord_2215523
  simp only [CollatzResearch.WordTrace]
  refine ⟨80806762352546027049043223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53871174901697351366028815 80806762352546027049043223)
  ·
    refine ⟨121210143528819040573564835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80806762352546027049043223 121210143528819040573564835)
    ·
      refine ⟨181815215293228560860347253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121210143528819040573564835 181815215293228560860347253)
      ·
        refine ⟨17045176433740177580657555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 181815215293228560860347253 17045176433740177580657555)
        ·
          refine ⟨25567764650610266370986333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17045176433740177580657555 25567764650610266370986333)
          ·
            refine ⟨9587911743978849889119875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25567764650610266370986333 9587911743978849889119875)
            ·
              refine ⟨14381867615968274833679813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9587911743978849889119875 14381867615968274833679813)
              ·
                refine ⟨2696600177994051531314965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14381867615968274833679813 2696600177994051531314965)
                ·
                  refine ⟨126403133343471165530389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2696600177994051531314965 126403133343471165530389)
                  ·
                    rfl

theorem cell23_2215523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 4, 6].length) (baseStart_2215523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215523 prefixEnd_2215523 := by exact prefixLift 2215523
  have htrace : WordTrace (prefixWord ++ tailWord_2215523) baseStart_2215523 baseEnd_2215523 := by
    simpa [prefixWord, tailWord_2215523, baseEnd_2215523] using wordTrace_append hprefix tailTrace_2215523
  have hstable : (prefixWord ++ tailWord_2215523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215523).length < 2 ^ (prefixWord ++ tailWord_2215523).sum := by decide
  have hdescent : baseEnd_2215523 < baseStart_2215523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215584 : List Nat := [2, 1, 1, 4, 3, 1, 2, 4, 1, 1, 3]
def baseStart_2215584 : Nat := 118140960795 + 2215584 * 2 ^ 59
def prefixEnd_2215584 : Nat := 4983230072969 + 3 ^ 40 * 2215584 * 2
def baseEnd_2215584 : Nat := 1137659522411164751110721

theorem tailTrace_2215584 : CollatzResearch.WordTrace tailWord_2215584 prefixEnd_2215584 1137659522411164751110721 := by
  unfold tailWord_2215584
  simp only [CollatzResearch.WordTrace]
  refine ⟨40404493602662517233506903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53872658136883356311342537 40404493602662517233506903)
  ·
    refine ⟨60606740403993775850260355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40404493602662517233506903 60606740403993775850260355)
    ·
      refine ⟨90910110605990663775390533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60606740403993775850260355 90910110605990663775390533)
      ·
        refine ⟨17045645738623249457885725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90910110605990663775390533 17045645738623249457885725)
        ·
          refine ⟨6392117151983718546707147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17045645738623249457885725 6392117151983718546707147)
          ·
            refine ⟨9588175727975577820060721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6392117151983718546707147 9588175727975577820060721)
            ·
              refine ⟨7191131795981683365045541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9588175727975577820060721 7191131795981683365045541)
              ·
                refine ⟨1348337211746565630946039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7191131795981683365045541 1348337211746565630946039)
                ·
                  refine ⟨2022505817619848446419059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1348337211746565630946039 2022505817619848446419059)
                  ·
                    refine ⟨3033758726429772669628589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2022505817619848446419059 3033758726429772669628589)
                    ·
                      refine ⟨1137659522411164751110721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3033758726429772669628589 1137659522411164751110721)
                      ·
                        rfl

theorem cell23_2215584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 4, 1, 1, 3].length) (baseStart_2215584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215584 prefixEnd_2215584 := by exact prefixLift 2215584
  have htrace : WordTrace (prefixWord ++ tailWord_2215584) baseStart_2215584 baseEnd_2215584 := by
    simpa [prefixWord, tailWord_2215584, baseEnd_2215584] using wordTrace_append hprefix tailTrace_2215584
  have hstable : (prefixWord ++ tailWord_2215584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215584).length < 2 ^ (prefixWord ++ tailWord_2215584).sum := by decide
  have hdescent : baseEnd_2215584 < baseStart_2215584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215600 : List Nat := [2, 1, 1, 1, 2, 1, 4, 5, 2, 4]
def baseStart_2215600 : Nat := 118140960795 + 2215600 * 2 ^ 59
def prefixEnd_2215600 : Nat := 4983230072969 + 3 ^ 40 * 2215600 * 2
def baseEnd_2215600 : Nat := 379222579367212229503549

theorem tailTrace_2215600 : CollatzResearch.WordTrace tailWord_2215600 prefixEnd_2215600 379222579367212229503549 := by
  unfold tailWord_2215600
  simp only [CollatzResearch.WordTrace]
  refine ⟨40404785386633534599798127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53873047182178046133064169 40404785386633534599798127)
  ·
    refine ⟨60607178079950301899697191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40404785386633534599798127 60607178079950301899697191)
    ·
      refine ⟨90910767119925452849545787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60607178079950301899697191 90910767119925452849545787)
      ·
        refine ⟨136366150679888179274318681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90910767119925452849545787 136366150679888179274318681)
        ·
          refine ⟨102274613009916134455739011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136366150679888179274318681 102274613009916134455739011)
          ·
            refine ⟨153411919514874201683608517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102274613009916134455739011 153411919514874201683608517)
            ·
              refine ⟨28764734909038912815676597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 153411919514874201683608517 28764734909038912815676597)
              ·
                refine ⟨2696693897722398076469681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28764734909038912815676597 2696693897722398076469681)
                ·
                  refine ⟨2022520423291798557352261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2696693897722398076469681 2022520423291798557352261)
                  ·
                    refine ⟨379222579367212229503549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2022520423291798557352261 379222579367212229503549)
                    ·
                      rfl

theorem cell23_2215600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 5, 2, 4].length) (baseStart_2215600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215600 prefixEnd_2215600 := by exact prefixLift 2215600
  have htrace : WordTrace (prefixWord ++ tailWord_2215600) baseStart_2215600 baseEnd_2215600 := by
    simpa [prefixWord, tailWord_2215600, baseEnd_2215600] using wordTrace_append hprefix tailTrace_2215600
  have hstable : (prefixWord ++ tailWord_2215600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215600).length < 2 ^ (prefixWord ++ tailWord_2215600).sum := by decide
  have hdescent : baseEnd_2215600 < baseStart_2215600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215603 : List Nat := [1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 6]
def baseStart_2215603 : Nat := 118140960795 + 2215603 * 2 ^ 59
def prefixEnd_2215603 : Nat := 4983230072969 + 3 ^ 40 * 2215603 * 2
def baseEnd_2215603 : Nat := 1137669278543600176773133

theorem tailTrace_2215603 : CollatzResearch.WordTrace tailWord_2215603 prefixEnd_2215603 1137669278543600176773133 := by
  unfold tailWord_2215603
  simp only [CollatzResearch.WordTrace]
  refine ⟨80809680192256200711955463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53873120128170800474636975 80809680192256200711955463)
  ·
    refine ⟨121214520288384301067933195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80809680192256200711955463 121214520288384301067933195)
    ·
      refine ⟨181821780432576451601899793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121214520288384301067933195 181821780432576451601899793)
      ·
        refine ⟨136366335324432338701424845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181821780432576451601899793 136366335324432338701424845)
        ·
          refine ⟨51137375746662127013034317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136366335324432338701424845 51137375746662127013034317)
          ·
            refine ⟨19176515904998297629887869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51137375746662127013034317 19176515904998297629887869)
            ·
              refine ⟨7191193464374361611207951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19176515904998297629887869 7191193464374361611207951)
              ·
                refine ⟨10786790196561542416811927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7191193464374361611207951 10786790196561542416811927)
                ·
                  refine ⟨16180185294842313625217891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10786790196561542416811927 16180185294842313625217891)
                  ·
                    refine ⟨24270277942263470437826837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16180185294842313625217891 24270277942263470437826837)
                    ·
                      refine ⟨1137669278543600176773133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24270277942263470437826837 1137669278543600176773133)
                      ·
                        rfl

theorem cell23_2215603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 6].length) (baseStart_2215603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215603 prefixEnd_2215603 := by exact prefixLift 2215603
  have htrace : WordTrace (prefixWord ++ tailWord_2215603) baseStart_2215603 baseEnd_2215603 := by
    simpa [prefixWord, tailWord_2215603, baseEnd_2215603] using wordTrace_append hprefix tailTrace_2215603
  have hstable : (prefixWord ++ tailWord_2215603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215603).length < 2 ^ (prefixWord ++ tailWord_2215603).sum := by decide
  have hdescent : baseEnd_2215603 < baseStart_2215603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215607 : List Nat := [1, 1, 3, 1, 5, 2, 2, 2, 1, 1, 4]
def baseStart_2215607 : Nat := 118140960795 + 2215607 * 2 ^ 59
def prefixEnd_2215607 : Nat := 4983230072969 + 3 ^ 40 * 2215607 * 2
def baseEnd_2215607 : Nat := 1137671332466218161123115

theorem tailTrace_2215607 : CollatzResearch.WordTrace tailWord_2215607 prefixEnd_2215607 1137671332466218161123115 := by
  unfold tailWord_2215607
  simp only [CollatzResearch.WordTrace]
  refine ⟨80809826084241709395101075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53873217389494472930067383 80809826084241709395101075)
  ·
    refine ⟨121214739126362564092651613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80809826084241709395101075 121214739126362564092651613)
    ·
      refine ⟨45455527172385961534744355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121214739126362564092651613 45455527172385961534744355)
      ·
        refine ⟨68183290758578942302116533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45455527172385961534744355 68183290758578942302116533)
        ·
          refine ⟨6392183508616775840823425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68183290758578942302116533 6392183508616775840823425)
          ·
            refine ⟨4794137631462581880617569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6392183508616775840823425 4794137631462581880617569)
            ·
              refine ⟨3595603223596936410463177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4794137631462581880617569 3595603223596936410463177)
              ·
                refine ⟨2696702417697702307847383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3595603223596936410463177 2696702417697702307847383)
                ·
                  refine ⟨4045053626546553461771075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2696702417697702307847383 4045053626546553461771075)
                  ·
                    refine ⟨6067580439819830192656613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4045053626546553461771075 6067580439819830192656613)
                    ·
                      refine ⟨1137671332466218161123115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6067580439819830192656613 1137671332466218161123115)
                      ·
                        rfl

theorem cell23_2215607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 2, 1, 1, 4].length) (baseStart_2215607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215607 prefixEnd_2215607 := by exact prefixLift 2215607
  have htrace : WordTrace (prefixWord ++ tailWord_2215607) baseStart_2215607 baseEnd_2215607 := by
    simpa [prefixWord, tailWord_2215607, baseEnd_2215607] using wordTrace_append hprefix tailTrace_2215607
  have hstable : (prefixWord ++ tailWord_2215607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215607).length < 2 ^ (prefixWord ++ tailWord_2215607).sum := by decide
  have hdescent : baseEnd_2215607 < baseStart_2215607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215613 : List Nat := [1, 4, 1, 2, 1, 2, 3, 9]
def baseStart_2215613 : Nat := 118140960795 + 2215613 * 2 ^ 59
def prefixEnd_2215613 : Nat := 4983230072969 + 3 ^ 40 * 2215613 * 2
def baseEnd_2215613 : Nat := 42136089383338708801781

theorem tailTrace_2215613 : CollatzResearch.WordTrace tailWord_2215613 prefixEnd_2215613 42136089383338708801781 := by
  unfold tailWord_2215613
  simp only [CollatzResearch.WordTrace]
  refine ⟨80810044922219972419819493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53873363281479981613212995 80810044922219972419819493)
  ·
    refine ⟨15151883422916244828716155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80810044922219972419819493 15151883422916244828716155)
    ·
      refine ⟨22727825134374367243074233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15151883422916244828716155 22727825134374367243074233)
      ·
        refine ⟨17045868850780775432305675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22727825134374367243074233 17045868850780775432305675)
        ·
          refine ⟨25568803276171163148458513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17045868850780775432305675 25568803276171163148458513)
          ·
            refine ⟨19176602457128372361343885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25568803276171163148458513 19176602457128372361343885)
            ·
              refine ⟨7191225921423139635503957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19176602457128372361343885 7191225921423139635503957)
              ·
                refine ⟨42136089383338708801781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7191225921423139635503957 42136089383338708801781)
                ·
                  rfl

theorem cell23_2215613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 9].length) (baseStart_2215613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215613 prefixEnd_2215613 := by exact prefixLift 2215613
  have htrace : WordTrace (prefixWord ++ tailWord_2215613) baseStart_2215613 baseEnd_2215613 := by
    simpa [prefixWord, tailWord_2215613, baseEnd_2215613] using wordTrace_append hprefix tailTrace_2215613
  have hstable : (prefixWord ++ tailWord_2215613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215613).length < 2 ^ (prefixWord ++ tailWord_2215613).sum := by decide
  have hdescent : baseEnd_2215613 < baseStart_2215613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215620 : List Nat := [2, 3, 3, 1, 1, 1, 2, 1, 3, 2, 4]
def baseStart_2215620 : Nat := 118140960795 + 2215620 * 2 ^ 59
def prefixEnd_2215620 : Nat := 4983230072969 + 3 ^ 40 * 2215620 * 2
def baseEnd_2215620 : Nat := 1137678007714726610260555

theorem tailTrace_2215620 : CollatzResearch.WordTrace tailWord_2215620 prefixEnd_2215620 1137678007714726610260555 := by
  unfold tailWord_2215620
  simp only [CollatzResearch.WordTrace]
  refine ⟨40405150116597306307662157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53873533488796408410216209 40405150116597306307662157)
  ·
    refine ⟨15151931293723989865373309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40405150116597306307662157 15151931293723989865373309)
    ·
      refine ⟨5681974235146496199514991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15151931293723989865373309 5681974235146496199514991)
      ·
        refine ⟨8522961352719744299272487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5681974235146496199514991 8522961352719744299272487)
        ·
          refine ⟨12784442029079616448908731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8522961352719744299272487 12784442029079616448908731)
          ·
            refine ⟨19176663043619424673363097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12784442029079616448908731 19176663043619424673363097)
            ·
              refine ⟨14382497282714568505022323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19176663043619424673363097 14382497282714568505022323)
              ·
                refine ⟨21573745924071852757533485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14382497282714568505022323 21573745924071852757533485)
                ·
                  refine ⟨8090154721526944784075057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21573745924071852757533485 8090154721526944784075057)
                  ·
                    refine ⟨6067616041145208588056293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8090154721526944784075057 6067616041145208588056293)
                    ·
                      refine ⟨1137678007714726610260555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6067616041145208588056293 1137678007714726610260555)
                      ·
                        rfl

theorem cell23_2215620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_2215620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215620 prefixEnd_2215620 := by exact prefixLift 2215620
  have htrace : WordTrace (prefixWord ++ tailWord_2215620) baseStart_2215620 baseEnd_2215620 := by
    simpa [prefixWord, tailWord_2215620, baseEnd_2215620] using wordTrace_append hprefix tailTrace_2215620
  have hstable : (prefixWord ++ tailWord_2215620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215620).length < 2 ^ (prefixWord ++ tailWord_2215620).sum := by decide
  have hdescent : baseEnd_2215620 < baseStart_2215620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215651 : List Nat := [1, 1, 1, 7, 2, 2, 2, 1, 2, 4]
def baseStart_2215651 : Nat := 118140960795 + 2215651 * 2 ^ 59
def prefixEnd_2215651 : Nat := 4983230072969 + 3 ^ 40 * 2215651 * 2
def baseEnd_2215651 : Nat := 379231308538338662990971

theorem tailTrace_2215651 : CollatzResearch.WordTrace tailWord_2215651 prefixEnd_2215651 379231308538338662990971 := by
  unfold tailWord_2215651
  simp only [CollatzResearch.WordTrace]
  refine ⟨80811430896082304909702807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53874287264054869939801871 80811430896082304909702807)
  ·
    refine ⟨121217146344123457364554211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80811430896082304909702807 121217146344123457364554211)
    ·
      refine ⟨181825719516185186046831317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121217146344123457364554211 181825719516185186046831317)
      ·
        refine ⟨4261540301160590297972609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 181825719516185186046831317 4261540301160590297972609)
        ·
          refine ⟨3196155225870442723479457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4261540301160590297972609 3196155225870442723479457)
          ·
            refine ⟨2397116419402832042609593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3196155225870442723479457 2397116419402832042609593)
            ·
              refine ⟨1797837314552124031957195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2397116419402832042609593 1797837314552124031957195)
              ·
                refine ⟨2696755971828186047935793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1797837314552124031957195 2696755971828186047935793)
                ·
                  refine ⟨2022566978871139535951845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2696755971828186047935793 2022566978871139535951845)
                  ·
                    refine ⟨379231308538338662990971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2022566978871139535951845 379231308538338662990971)
                    ·
                      rfl

theorem cell23_2215651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 1, 2, 4].length) (baseStart_2215651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215651 prefixEnd_2215651 := by exact prefixLift 2215651
  have htrace : WordTrace (prefixWord ++ tailWord_2215651) baseStart_2215651 baseEnd_2215651 := by
    simpa [prefixWord, tailWord_2215651, baseEnd_2215651] using wordTrace_append hprefix tailTrace_2215651
  have hstable : (prefixWord ++ tailWord_2215651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215651).length < 2 ^ (prefixWord ++ tailWord_2215651).sum := by decide
  have hdescent : baseEnd_2215651 < baseStart_2215651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215673 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 6, 6]
def baseStart_2215673 : Nat := 118140960795 + 2215673 * 2 ^ 59
def prefixEnd_2215673 : Nat := 4983230072969 + 3 ^ 40 * 2215673 * 2
def baseEnd_2215673 : Nat := 379235074063138300965937

theorem tailTrace_2215673 : CollatzResearch.WordTrace tailWord_2215673 prefixEnd_2215673 379235074063138300965937 := by
  unfold tailWord_2215673
  simp only [CollatzResearch.WordTrace]
  refine ⟨80812233302002602667003673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53874822201335068444669115 80812233302002602667003673)
  ·
    refine ⟨60609174976501952000252755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80812233302002602667003673 60609174976501952000252755)
    ·
      refine ⟨90913762464752928000379133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60609174976501952000252755 90913762464752928000379133)
      ·
        refine ⟨34092660924282348000142175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90913762464752928000379133 34092660924282348000142175)
        ·
          refine ⟨51138991386423522000213263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34092660924282348000142175 51138991386423522000213263)
          ·
            refine ⟨76708487079635283000319895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51138991386423522000213263 76708487079635283000319895)
            ·
              refine ⟨115062730619452924500479843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76708487079635283000319895 115062730619452924500479843)
              ·
                refine ⟨172594095929179386750719765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115062730619452924500479843 172594095929179386750719765)
                ·
                  refine ⟨8090348246680283753939989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 172594095929179386750719765 8090348246680283753939989)
                  ·
                    refine ⟨379235074063138300965937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8090348246680283753939989 379235074063138300965937)
                    ·
                      rfl

theorem cell23_2215673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 6].length) (baseStart_2215673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215673 prefixEnd_2215673 := by exact prefixLift 2215673
  have htrace : WordTrace (prefixWord ++ tailWord_2215673) baseStart_2215673 baseEnd_2215673 := by
    simpa [prefixWord, tailWord_2215673, baseEnd_2215673] using wordTrace_append hprefix tailTrace_2215673
  have hstable : (prefixWord ++ tailWord_2215673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215673).length < 2 ^ (prefixWord ++ tailWord_2215673).sum := by decide
  have hdescent : baseEnd_2215673 < baseStart_2215673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215686 : List Nat := [6, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3]
def baseStart_2215686 : Nat := 118140960795 + 2215686 * 2 ^ 59
def prefixEnd_2215686 : Nat := 4983230072969 + 3 ^ 40 * 2215686 * 2
def baseEnd_2215686 : Nat := 1137711897437923352035253

theorem tailTrace_2215686 : CollatzResearch.WordTrace tailWord_2215686 prefixEnd_2215686 1137711897437923352035253 := by
  unfold tailWord_2215686
  simp only [CollatzResearch.WordTrace]
  refine ⟨2525397107842359558975841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 53875138300637003924817941 2525397107842359558975841)
  ·
    refine ⟨1894047830881769669231881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2525397107842359558975841 1894047830881769669231881)
    ·
      refine ⟨1420535873161327251923911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1894047830881769669231881 1420535873161327251923911)
      ·
        refine ⟨2130803809741990877885867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1420535873161327251923911 2130803809741990877885867)
        ·
          refine ⟨3196205714612986316828801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2130803809741990877885867 3196205714612986316828801)
          ·
            refine ⟨2397154285959739737621601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3196205714612986316828801 2397154285959739737621601)
            ·
              refine ⟨1797865714469804803216201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2397154285959739737621601 1797865714469804803216201)
              ·
                refine ⟨1348399285852353602412151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1797865714469804803216201 1348399285852353602412151)
                ·
                  refine ⟨2022598928778530403618227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1348399285852353602412151 2022598928778530403618227)
                  ·
                    refine ⟨3033898393167795605427341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2022598928778530403618227 3033898393167795605427341)
                    ·
                      refine ⟨1137711897437923352035253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3033898393167795605427341 1137711897437923352035253)
                      ·
                        rfl

theorem cell23_2215686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_2215686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215686 prefixEnd_2215686 := by exact prefixLift 2215686
  have htrace : WordTrace (prefixWord ++ tailWord_2215686) baseStart_2215686 baseEnd_2215686 := by
    simpa [prefixWord, tailWord_2215686, baseEnd_2215686] using wordTrace_append hprefix tailTrace_2215686
  have hstable : (prefixWord ++ tailWord_2215686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215686).length < 2 ^ (prefixWord ++ tailWord_2215686).sum := by decide
  have hdescent : baseEnd_2215686 < baseStart_2215686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215714 : List Nat := [3, 3, 1, 1, 2, 1, 4, 1, 1, 4, 2]
def baseStart_2215714 : Nat := 118140960795 + 2215714 * 2 ^ 59
def prefixEnd_2215714 : Nat := 4983230072969 + 3 ^ 40 * 2215714 * 2
def baseEnd_2215714 : Nat := 1137726274896249242485123

theorem tailTrace_2215714 : CollatzResearch.WordTrace tailWord_2215714 prefixEnd_2215714 1137726274896249242485123 := by
  unfold tailWord_2215714
  simp only [CollatzResearch.WordTrace]
  refine ⟨20203432173713516667311549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53875819129902711112830797 20203432173713516667311549)
  ·
    refine ⟨7576287065142568750241831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20203432173713516667311549 7576287065142568750241831)
    ·
      refine ⟨11364430597713853125362747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7576287065142568750241831 11364430597713853125362747)
      ·
        refine ⟨17046645896570779688044121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11364430597713853125362747 17046645896570779688044121)
        ·
          refine ⟨12784984422428084766033091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17046645896570779688044121 12784984422428084766033091)
          ·
            refine ⟨19177476633642127149049637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12784984422428084766033091 19177476633642127149049637)
            ·
              refine ⟨3595776868807898840446807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19177476633642127149049637 3595776868807898840446807)
              ·
                refine ⟨5393665303211848260670211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3595776868807898840446807 5393665303211848260670211)
                ·
                  refine ⟨8090497954817772391005317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5393665303211848260670211 8090497954817772391005317)
                  ·
                    refine ⟨1516968366528332323313497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8090497954817772391005317 1516968366528332323313497)
                    ·
                      refine ⟨1137726274896249242485123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1516968366528332323313497 1137726274896249242485123)
                      ·
                        rfl

theorem cell23_2215714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 1, 4, 2].length) (baseStart_2215714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215714 prefixEnd_2215714 := by exact prefixLift 2215714
  have htrace : WordTrace (prefixWord ++ tailWord_2215714) baseStart_2215714 baseEnd_2215714 := by
    simpa [prefixWord, tailWord_2215714, baseEnd_2215714] using wordTrace_append hprefix tailTrace_2215714
  have hstable : (prefixWord ++ tailWord_2215714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215714).length < 2 ^ (prefixWord ++ tailWord_2215714).sum := by decide
  have hdescent : baseEnd_2215714 < baseStart_2215714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215720 : List Nat := [2, 1, 5, 1, 1, 2, 1, 1, 9]
def baseStart_2215720 : Nat := 118140960795 + 2215720 * 2 ^ 59
def prefixEnd_2215720 : Nat := 4983230072969 + 3 ^ 40 * 2215720 * 2
def baseEnd_2215720 : Nat := 126414372864464024334455

theorem tailTrace_2215720 : CollatzResearch.WordTrace tailWord_2215720 prefixEnd_2215720 126414372864464024334455 := by
  unfold tailWord_2215720
  simp only [CollatzResearch.WordTrace]
  refine ⟨40406973766416164846982307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53875965021888219795976409 40406973766416164846982307)
  ·
    refine ⟨60610460649624247270473461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40406973766416164846982307 60610460649624247270473461)
    ·
      refine ⟨5682230685902273181606887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60610460649624247270473461 5682230685902273181606887)
      ·
        refine ⟨8523346028853409772410331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5682230685902273181606887 8523346028853409772410331)
        ·
          refine ⟨12785019043280114658615497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8523346028853409772410331 12785019043280114658615497)
          ·
            refine ⟨9588764282460085993961623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12785019043280114658615497 9588764282460085993961623)
            ·
              refine ⟨14383146423690128990942435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9588764282460085993961623 14383146423690128990942435)
              ·
                refine ⟨21574719635535193486413653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14383146423690128990942435 21574719635535193486413653)
                ·
                  refine ⟨126414372864464024334455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 21574719635535193486413653 126414372864464024334455)
                  ·
                    rfl

theorem cell23_2215720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 9].length) (baseStart_2215720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215720 prefixEnd_2215720 := by exact prefixLift 2215720
  have htrace : WordTrace (prefixWord ++ tailWord_2215720) baseStart_2215720 baseEnd_2215720 := by
    simpa [prefixWord, tailWord_2215720, baseEnd_2215720] using wordTrace_append hprefix tailTrace_2215720
  have hstable : (prefixWord ++ tailWord_2215720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215720).length < 2 ^ (prefixWord ++ tailWord_2215720).sum := by decide
  have hdescent : baseEnd_2215720 < baseStart_2215720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215723 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 6]
def baseStart_2215723 : Nat := 118140960795 + 2215723 * 2 ^ 59
def prefixEnd_2215723 : Nat := 4983230072969 + 3 ^ 40 * 2215723 * 2
def baseEnd_2215723 : Nat := 1137730896222139707272581

theorem tailTrace_2215723 : CollatzResearch.WordTrace tailWord_2215723 prefixEnd_2215723 1137730896222139707272581 := by
  unfold tailWord_2215723
  simp only [CollatzResearch.WordTrace]
  refine ⟨80814056951821461206323823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53876037967880974137549215 80814056951821461206323823)
  ·
    refine ⟨121221085427732191809485735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80814056951821461206323823 121221085427732191809485735)
    ·
      refine ⟨181831628141598287714228603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121221085427732191809485735 181831628141598287714228603)
      ·
        refine ⟨272747442212397431571342905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181831628141598287714228603 272747442212397431571342905)
        ·
          refine ⟨204560581659298073678507179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 272747442212397431571342905 204560581659298073678507179)
          ·
            refine ⟨306840872488947110517760769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204560581659298073678507179 306840872488947110517760769)
            ·
              refine ⟨230130654366710332888320577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 306840872488947110517760769 230130654366710332888320577)
              ·
                refine ⟨172597990775032749666240433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 230130654366710332888320577 172597990775032749666240433)
                ·
                  refine ⟨129448493081274562249680325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 172597990775032749666240433 129448493081274562249680325)
                  ·
                    refine ⟨24271592452738980421815061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 129448493081274562249680325 24271592452738980421815061)
                    ·
                      refine ⟨1137730896222139707272581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24271592452738980421815061 1137730896222139707272581)
                      ·
                        rfl

theorem cell23_2215723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 6].length) (baseStart_2215723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215723 prefixEnd_2215723 := by exact prefixLift 2215723
  have htrace : WordTrace (prefixWord ++ tailWord_2215723) baseStart_2215723 baseEnd_2215723 := by
    simpa [prefixWord, tailWord_2215723, baseEnd_2215723] using wordTrace_append hprefix tailTrace_2215723
  have hstable : (prefixWord ++ tailWord_2215723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215723).length < 2 ^ (prefixWord ++ tailWord_2215723).sum := by decide
  have hdescent : baseEnd_2215723 < baseStart_2215723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215770 : List Nat := [3, 1, 1, 2, 1, 3, 1, 1, 3, 3, 4]
def baseStart_2215770 : Nat := 118140960795 + 2215770 * 2 ^ 59
def prefixEnd_2215770 : Nat := 4983230072969 + 3 ^ 40 * 2215770 * 2
def baseEnd_2215770 : Nat := 1137755029812901023384865

theorem tailTrace_2215770 : CollatzResearch.WordTrace tailWord_2215770 prefixEnd_2215770 1137755029812901023384865 := by
  unfold tailWord_2215770
  simp only [CollatzResearch.WordTrace]
  refine ⟨20203942795662797058321191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53877180788434125488856509 20203942795662797058321191)
  ·
    refine ⟨30305914193494195587481787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20203942795662797058321191 30305914193494195587481787)
    ·
      refine ⟨45458871290241293381222681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30305914193494195587481787 45458871290241293381222681)
      ·
        refine ⟨34094153467680970035917011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45458871290241293381222681 34094153467680970035917011)
        ·
          refine ⟨51141230201521455053875517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34094153467680970035917011 51141230201521455053875517)
          ·
            refine ⟨19177961325570545645203319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51141230201521455053875517 19177961325570545645203319)
            ·
              refine ⟨28766941988355818467804979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19177961325570545645203319 28766941988355818467804979)
              ·
                refine ⟨43150412982533727701707469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28766941988355818467804979 43150412982533727701707469)
                ·
                  refine ⟨16181404868450147888140301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43150412982533727701707469 16181404868450147888140301)
                  ·
                    refine ⟨6068026825668805458052613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16181404868450147888140301 6068026825668805458052613)
                    ·
                      refine ⟨1137755029812901023384865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6068026825668805458052613 1137755029812901023384865)
                      ·
                        rfl

theorem cell23_2215770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_2215770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215770 prefixEnd_2215770 := by exact prefixLift 2215770
  have htrace : WordTrace (prefixWord ++ tailWord_2215770) baseStart_2215770 baseEnd_2215770 := by
    simpa [prefixWord, tailWord_2215770, baseEnd_2215770] using wordTrace_append hprefix tailTrace_2215770
  have hstable : (prefixWord ++ tailWord_2215770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215770).length < 2 ^ (prefixWord ++ tailWord_2215770).sum := by decide
  have hdescent : baseEnd_2215770 < baseStart_2215770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215838 : List Nat := [4, 3, 1, 3, 1, 1, 2, 1, 2, 1, 4]
def baseStart_2215838 : Nat := 118140960795 + 2215838 * 2 ^ 59
def prefixEnd_2215838 : Nat := 4983230072969 + 3 ^ 40 * 2215838 * 2
def baseEnd_2215838 : Nat := 1137789946497406757334553

theorem tailTrace_2215838 : CollatzResearch.WordTrace tailWord_2215838 prefixEnd_2215838 1137789946497406757334553 := by
  unfold tailWord_2215838
  simp only [CollatzResearch.WordTrace]
  refine ⟨10102281418300604480845021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53878834230936557231173445 10102281418300604480845021)
  ·
    refine ⟨3788355531862726680316883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10102281418300604480845021 3788355531862726680316883)
    ·
      refine ⟨5682533297794090020475325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3788355531862726680316883 5682533297794090020475325)
      ·
        refine ⟨2130949986672783757678247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5682533297794090020475325 2130949986672783757678247)
        ·
          refine ⟨3196424980009175636517371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2130949986672783757678247 3196424980009175636517371)
          ·
            refine ⟨4794637470013763454776057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3196424980009175636517371 4794637470013763454776057)
            ·
              refine ⟨3595978102510322591082043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4794637470013763454776057 3595978102510322591082043)
              ·
                refine ⟨5393967153765483886623065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3595978102510322591082043 5393967153765483886623065)
                ·
                  refine ⟨4045475365324112914967299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5393967153765483886623065 4045475365324112914967299)
                  ·
                    refine ⟨6068213047986169372450949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4045475365324112914967299 6068213047986169372450949)
                    ·
                      refine ⟨1137789946497406757334553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6068213047986169372450949 1137789946497406757334553)
                      ·
                        rfl

theorem cell23_2215838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_2215838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215838 prefixEnd_2215838 := by exact prefixLift 2215838
  have htrace : WordTrace (prefixWord ++ tailWord_2215838) baseStart_2215838 baseEnd_2215838 := by
    simpa [prefixWord, tailWord_2215838, baseEnd_2215838] using wordTrace_append hprefix tailTrace_2215838
  have hstable : (prefixWord ++ tailWord_2215838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215838).length < 2 ^ (prefixWord ++ tailWord_2215838).sum := by decide
  have hdescent : baseEnd_2215838 < baseStart_2215838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215841 : List Nat := [1, 2, 3, 4, 2, 1, 2, 1, 2, 2, 3]
def baseStart_2215841 : Nat := 118140960795 + 2215841 * 2 ^ 59
def prefixEnd_2215841 : Nat := 4983230072969 + 3 ^ 40 * 2215841 * 2
def baseEnd_2215841 : Nat := 1137791486939370245597039

theorem tailTrace_2215841 : CollatzResearch.WordTrace tailWord_2215841 prefixEnd_2215841 1137791486939370245597039 := by
  unfold tailWord_2215841
  simp only [CollatzResearch.WordTrace]
  refine ⟨80818360765393967359119377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53878907176929311572746251 80818360765393967359119377)
  ·
    refine ⟨60613770574045475519339533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80818360765393967359119377 60613770574045475519339533)
    ·
      refine ⟨22730163965267053319752325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60613770574045475519339533 22730163965267053319752325)
      ·
        refine ⟨4261905743487572497453561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22730163965267053319752325 4261905743487572497453561)
        ·
          refine ⟨3196429307615679373090171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4261905743487572497453561 3196429307615679373090171)
          ·
            refine ⟨4794643961423519059635257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3196429307615679373090171 4794643961423519059635257)
            ·
              refine ⟨3595982971067639294726443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4794643961423519059635257 3595982971067639294726443)
              ·
                refine ⟨5393974456601458942089665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3595982971067639294726443 5393974456601458942089665)
                ·
                  refine ⟨4045480842451094206567249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5393974456601458942089665 4045480842451094206567249)
                  ·
                    refine ⟨3034110631838320654925437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4045480842451094206567249 3034110631838320654925437)
                    ·
                      refine ⟨1137791486939370245597039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3034110631838320654925437 1137791486939370245597039)
                      ·
                        rfl

theorem cell23_2215841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_2215841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215841 prefixEnd_2215841 := by exact prefixLift 2215841
  have htrace : WordTrace (prefixWord ++ tailWord_2215841) baseStart_2215841 baseEnd_2215841 := by
    simpa [prefixWord, tailWord_2215841, baseEnd_2215841] using wordTrace_append hprefix tailTrace_2215841
  have hstable : (prefixWord ++ tailWord_2215841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215841).length < 2 ^ (prefixWord ++ tailWord_2215841).sum := by decide
  have hdescent : baseEnd_2215841 < baseStart_2215841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215864 : List Nat := [2, 1, 2, 1, 2, 3, 1, 4, 2, 3, 2]
def baseStart_2215864 : Nat := 118140960795 + 2215864 * 2 ^ 59
def prefixEnd_2215864 : Nat := 4983230072969 + 3 ^ 40 * 2215864 * 2
def baseEnd_2215864 : Nat := 1137803296994423655609433

theorem tailTrace_2215864 : CollatzResearch.WordTrace tailWord_2215864 prefixEnd_2215864 1137803296994423655609433 := by
  unfold tailWord_2215864
  simp only [CollatzResearch.WordTrace]
  refine ⟨40409599822155321143603323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53879466429540428191471097 40409599822155321143603323)
  ·
    refine ⟨60614399733232981715404985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40409599822155321143603323 60614399733232981715404985)
    ·
      refine ⟨45460799799924736286553739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60614399733232981715404985 45460799799924736286553739)
      ·
        refine ⟨68191199699887104429830609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45460799799924736286553739 68191199699887104429830609)
        ·
          refine ⟨51143399774915328322372957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68191199699887104429830609 51143399774915328322372957)
          ·
            refine ⟨19178774915593248120889859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51143399774915328322372957 19178774915593248120889859)
            ·
              refine ⟨28768162373389872181334789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19178774915593248120889859 28768162373389872181334789)
              ·
                refine ⟨5394030445010601034000273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28768162373389872181334789 5394030445010601034000273)
                ·
                  refine ⟨4045522833757950775500205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5394030445010601034000273 4045522833757950775500205)
                  ·
                    refine ⟨1517071062659231540812577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4045522833757950775500205 1517071062659231540812577)
                    ·
                      refine ⟨1137803296994423655609433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1517071062659231540812577 1137803296994423655609433)
                      ·
                        rfl

theorem cell23_2215864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 2, 3, 2].length) (baseStart_2215864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215864 prefixEnd_2215864 := by exact prefixLift 2215864
  have htrace : WordTrace (prefixWord ++ tailWord_2215864) baseStart_2215864 baseEnd_2215864 := by
    simpa [prefixWord, tailWord_2215864, baseEnd_2215864] using wordTrace_append hprefix tailTrace_2215864
  have hstable : (prefixWord ++ tailWord_2215864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215864).length < 2 ^ (prefixWord ++ tailWord_2215864).sum := by decide
  have hdescent : baseEnd_2215864 < baseStart_2215864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215871 : List Nat := [1, 1, 2, 2, 2, 1, 5, 4, 1, 1, 3]
def baseStart_2215871 : Nat := 118140960795 + 2215871 * 2 ^ 59
def prefixEnd_2215871 : Nat := 4983230072969 + 3 ^ 40 * 2215871 * 2
def baseEnd_2215871 : Nat := 1137806891359005128221901

theorem tailTrace_2215871 : CollatzResearch.WordTrace tailWord_2215871 prefixEnd_2215871 1137806891359005128221901 := by
  unfold tailWord_2215871
  simp only [CollatzResearch.WordTrace]
  refine ⟨80819454955285282482711467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53879636636856854988474311 80819454955285282482711467)
  ·
    refine ⟨121229182432927923724067201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80819454955285282482711467 121229182432927923724067201)
    ·
      refine ⟨90921886824695942793050401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121229182432927923724067201 90921886824695942793050401)
      ·
        refine ⟨68191415118521957094787801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90921886824695942793050401 68191415118521957094787801)
        ·
          refine ⟨51143561338891467821090851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68191415118521957094787801 51143561338891467821090851)
          ·
            refine ⟨76715342008337201731636277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51143561338891467821090851 76715342008337201731636277)
            ·
              refine ⟨7192063313281612662340901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76715342008337201731636277 7192063313281612662340901)
              ·
                refine ⟨1348511871240302374188919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7192063313281612662340901 1348511871240302374188919)
                ·
                  refine ⟨2022767806860453561283379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1348511871240302374188919 2022767806860453561283379)
                  ·
                    refine ⟨3034151710290680341925069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2022767806860453561283379 3034151710290680341925069)
                    ·
                      refine ⟨1137806891359005128221901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3034151710290680341925069 1137806891359005128221901)
                      ·
                        rfl

theorem cell23_2215871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 4, 1, 1, 3].length) (baseStart_2215871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215871 prefixEnd_2215871 := by exact prefixLift 2215871
  have htrace : WordTrace (prefixWord ++ tailWord_2215871) baseStart_2215871 baseEnd_2215871 := by
    simpa [prefixWord, tailWord_2215871, baseEnd_2215871] using wordTrace_append hprefix tailTrace_2215871
  have hstable : (prefixWord ++ tailWord_2215871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215871).length < 2 ^ (prefixWord ++ tailWord_2215871).sum := by decide
  have hdescent : baseEnd_2215871 < baseStart_2215871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215887 : List Nat := [1, 1, 2, 1, 1, 5, 4, 1, 1, 6]
def baseStart_2215887 : Nat := 118140960795 + 2215887 * 2 ^ 59
def prefixEnd_2215887 : Nat := 4983230072969 + 3 ^ 40 * 2215887 * 2
def baseEnd_2215887 : Nat := 379271702349825688540609

theorem tailTrace_2215887 : CollatzResearch.WordTrace tailWord_2215887 prefixEnd_2215887 379271702349825688540609 := by
  unfold tailWord_2215887
  simp only [CollatzResearch.WordTrace]
  refine ⟨80820038523227317215293915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53880025682151544810195943 80820038523227317215293915)
  ·
    refine ⟨121230057784840975822940873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80820038523227317215293915 121230057784840975822940873)
    ·
      refine ⟨90922543338630731867205655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121230057784840975822940873 90922543338630731867205655)
      ·
        refine ⟨136383815007946097800808483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90922543338630731867205655 136383815007946097800808483)
        ·
          refine ⟨204575722511919146701212725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136383815007946097800808483 204575722511919146701212725)
          ·
            refine ⟨19178973985492420003238693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 204575722511919146701212725 19178973985492420003238693)
            ·
              refine ⟨3596057622279828750607255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19178973985492420003238693 3596057622279828750607255)
              ·
                refine ⟨5394086433419743125910883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3596057622279828750607255 5394086433419743125910883)
                ·
                  refine ⟨8091129650129614688866325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5394086433419743125910883 8091129650129614688866325)
                  ·
                    refine ⟨379271702349825688540609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8091129650129614688866325 379271702349825688540609)
                    ·
                      rfl

theorem cell23_2215887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 6].length) (baseStart_2215887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215887 prefixEnd_2215887 := by exact prefixLift 2215887
  have htrace : WordTrace (prefixWord ++ tailWord_2215887) baseStart_2215887 baseEnd_2215887 := by
    simpa [prefixWord, tailWord_2215887, baseEnd_2215887] using wordTrace_append hprefix tailTrace_2215887
  have hstable : (prefixWord ++ tailWord_2215887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215887).length < 2 ^ (prefixWord ++ tailWord_2215887).sum := by decide
  have hdescent : baseEnd_2215887 < baseStart_2215887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215898 : List Nat := [3, 1, 1, 2, 5, 2, 1, 1, 2, 3, 2]
def baseStart_2215898 : Nat := 118140960795 + 2215898 * 2 ^ 59
def prefixEnd_2215898 : Nat := 4983230072969 + 3 ^ 40 * 2215898 * 2
def baseEnd_2215898 : Nat := 1137820755336676522584277

theorem tailTrace_2215898 : CollatzResearch.WordTrace tailWord_2215898 prefixEnd_2215898 1137820755336676522584277 := by
  unfold tailWord_2215898
  simp only [CollatzResearch.WordTrace]
  refine ⟨20205109931546866523486087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53880293150791644062629565 20205109931546866523486087)
  ·
    refine ⟨30307664897320299785229131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20205109931546866523486087 30307664897320299785229131)
    ·
      refine ⟨45461497345980449677843697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30307664897320299785229131 45461497345980449677843697)
      ·
        refine ⟨34096123009485337258382773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45461497345980449677843697 34096123009485337258382773)
        ·
          refine ⟨3196511532139250367973385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34096123009485337258382773 3196511532139250367973385)
          ·
            refine ⟨2397383649104437775980039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3196511532139250367973385 2397383649104437775980039)
            ·
              refine ⟨3596075473656656663970059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2397383649104437775980039 3596075473656656663970059)
              ·
                refine ⟨5394113210484984995955089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3596075473656656663970059 5394113210484984995955089)
                ·
                  refine ⟨4045584907863738746966317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5394113210484984995955089 4045584907863738746966317)
                  ·
                    refine ⟨1517094340448902030112369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4045584907863738746966317 1517094340448902030112369)
                    ·
                      refine ⟨1137820755336676522584277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1517094340448902030112369 1137820755336676522584277)
                      ·
                        rfl

theorem cell23_2215898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 2, 3, 2].length) (baseStart_2215898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215898 prefixEnd_2215898 := by exact prefixLift 2215898
  have htrace : WordTrace (prefixWord ++ tailWord_2215898) baseStart_2215898 baseEnd_2215898 := by
    simpa [prefixWord, tailWord_2215898, baseEnd_2215898] using wordTrace_append hprefix tailTrace_2215898
  have hstable : (prefixWord ++ tailWord_2215898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215898).length < 2 ^ (prefixWord ++ tailWord_2215898).sum := by decide
  have hdescent : baseEnd_2215898 < baseStart_2215898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215911 : List Nat := [1, 1, 5, 2, 3, 1, 1, 3, 1, 1, 4]
def baseStart_2215911 : Nat := 118140960795 + 2215911 * 2 ^ 59
def prefixEnd_2215911 : Nat := 4983230072969 + 3 ^ 40 * 2215911 * 2
def baseEnd_2215911 : Nat := 1137827430585184971721717

theorem tailTrace_2215911 : CollatzResearch.WordTrace tailWord_2215911 prefixEnd_2215911 1137827430585184971721717 := by
  unfold tailWord_2215911
  simp only [CollatzResearch.WordTrace]
  refine ⟨80820913875140369314167587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53880609250093579542778391 80820913875140369314167587)
  ·
    refine ⟨121231370812710553971251381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80820913875140369314167587 121231370812710553971251381)
    ·
      refine ⟨11365441013691614434804817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 121231370812710553971251381 11365441013691614434804817)
      ·
        refine ⟨8524080760268710826103613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11365441013691614434804817 8524080760268710826103613)
        ·
          refine ⟨3196530285100766559788855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8524080760268710826103613 3196530285100766559788855)
          ·
            refine ⟨4794795427651149839683283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3196530285100766559788855 4794795427651149839683283)
            ·
              refine ⟨7192193141476724759524925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4794795427651149839683283 7192193141476724759524925)
              ·
                refine ⟨2697072428053771784821847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7192193141476724759524925 2697072428053771784821847)
                ·
                  refine ⟨4045608642080657677232771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2697072428053771784821847 4045608642080657677232771)
                  ·
                    refine ⟨6068412963120986515849157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4045608642080657677232771 6068412963120986515849157)
                    ·
                      refine ⟨1137827430585184971721717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6068412963120986515849157 1137827430585184971721717)
                      ·
                        rfl

theorem cell23_2215911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_2215911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215911 prefixEnd_2215911 := by exact prefixLift 2215911
  have htrace : WordTrace (prefixWord ++ tailWord_2215911) baseStart_2215911 baseEnd_2215911 := by
    simpa [prefixWord, tailWord_2215911, baseEnd_2215911] using wordTrace_append hprefix tailTrace_2215911
  have hstable : (prefixWord ++ tailWord_2215911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215911).length < 2 ^ (prefixWord ++ tailWord_2215911).sum := by decide
  have hdescent : baseEnd_2215911 < baseStart_2215911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215928 : List Nat := [2, 1, 2, 1, 1, 3, 4, 4, 1, 2, 2]
def baseStart_2215928 : Nat := 118140960795 + 2215928 * 2 ^ 59
def prefixEnd_2215928 : Nat := 4983230072969 + 3 ^ 40 * 2215928 * 2
def baseEnd_2215928 : Nat := 1137836159756311405209139

theorem tailTrace_2215928 : CollatzResearch.WordTrace tailWord_2215928 prefixEnd_2215928 1137836159756311405209139 := by
  unfold tailWord_2215928
  simp only [CollatzResearch.WordTrace]
  refine ⟨40410766958039390608768219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53881022610719187478357625 40410766958039390608768219)
  ·
    refine ⟨60616150437059085913152329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40410766958039390608768219 60616150437059085913152329)
    ·
      refine ⟨45462112827794314434864247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60616150437059085913152329 45462112827794314434864247)
      ·
        refine ⟨68193169241691471652296371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45462112827794314434864247 68193169241691471652296371)
        ·
          refine ⟨102289753862537207478444557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68193169241691471652296371 102289753862537207478444557)
          ·
            refine ⟨38358657698451452804416709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102289753862537207478444557 38358657698451452804416709)
            ·
              refine ⟨7192248318459647400828133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38358657698451452804416709 7192248318459647400828133)
              ·
                refine ⟨1348546559711183887655275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7192248318459647400828133 1348546559711183887655275)
                ·
                  refine ⟨2022819839566775831482913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1348546559711183887655275 2022819839566775831482913)
                  ·
                    refine ⟨1517114879675081873612185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2022819839566775831482913 1517114879675081873612185)
                    ·
                      refine ⟨1137836159756311405209139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1517114879675081873612185 1137836159756311405209139)
                      ·
                        rfl

theorem cell23_2215928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 4, 1, 2, 2].length) (baseStart_2215928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215928 prefixEnd_2215928 := by exact prefixLift 2215928
  have htrace : WordTrace (prefixWord ++ tailWord_2215928) baseStart_2215928 baseEnd_2215928 := by
    simpa [prefixWord, tailWord_2215928, baseEnd_2215928] using wordTrace_append hprefix tailTrace_2215928
  have hstable : (prefixWord ++ tailWord_2215928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215928).length < 2 ^ (prefixWord ++ tailWord_2215928).sum := by decide
  have hdescent : baseEnd_2215928 < baseStart_2215928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215942 : List Nat := [6, 2, 1, 2, 1, 1, 2, 2, 1, 5]
def baseStart_2215942 : Nat := 118140960795 + 2215942 * 2 ^ 59
def prefixEnd_2215942 : Nat := 4983230072969 + 3 ^ 40 * 2215942 * 2
def baseEnd_2215942 : Nat := 379281116161824783478025

theorem tailTrace_2215942 : CollatzResearch.WordTrace tailWord_2215942 prefixEnd_2215942 379281116161824783478025 := by
  unfold tailWord_2215942
  simp only [CollatzResearch.WordTrace]
  refine ⟨2525688891813376925267065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 53881363025352041072364053 2525688891813376925267065)
  ·
    refine ⟨1894266668860032693950299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2525688891813376925267065 1894266668860032693950299)
    ·
      refine ⟨2841400003290049040925449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1894266668860032693950299 2841400003290049040925449)
      ·
        refine ⟨2131050002467536780694087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2841400003290049040925449 2131050002467536780694087)
        ·
          refine ⟨3196575003701305171041131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2131050002467536780694087 3196575003701305171041131)
          ·
            refine ⟨4794862505551957756561697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3196575003701305171041131 4794862505551957756561697)
            ·
              refine ⟨3596146879163968317421273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4794862505551957756561697 3596146879163968317421273)
              ·
                refine ⟨2697110159372976238065955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3596146879163968317421273 2697110159372976238065955)
                ·
                  refine ⟨4045665239059464357098933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2697110159372976238065955 4045665239059464357098933)
                  ·
                    refine ⟨379281116161824783478025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4045665239059464357098933 379281116161824783478025)
                    ·
                      rfl

theorem cell23_2215942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_2215942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215942 prefixEnd_2215942 := by exact prefixLift 2215942
  have htrace : WordTrace (prefixWord ++ tailWord_2215942) baseStart_2215942 baseEnd_2215942 := by
    simpa [prefixWord, tailWord_2215942, baseEnd_2215942] using wordTrace_append hprefix tailTrace_2215942
  have hstable : (prefixWord ++ tailWord_2215942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215942).length < 2 ^ (prefixWord ++ tailWord_2215942).sum := by decide
  have hdescent : baseEnd_2215942 < baseStart_2215942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2215971 : List Nat := [1, 1, 1, 4, 3, 1, 1, 5, 1, 3, 2]
def baseStart_2215971 : Nat := 118140960795 + 2215971 * 2 ^ 59
def prefixEnd_2215971 : Nat := 4983230072969 + 3 ^ 40 * 2215971 * 2
def baseEnd_2215971 : Nat := 1137858239424454736971441

theorem tailTrace_2215971 : CollatzResearch.WordTrace tailWord_2215971 prefixEnd_2215971 1137858239424454736971441 := by
  unfold tailWord_2215971
  simp only [CollatzResearch.WordTrace]
  refine ⟨80823102254922999561351767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53882068169948666374234511 80823102254922999561351767)
  ·
    refine ⟨121234653382384499342027651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80823102254922999561351767 121234653382384499342027651)
    ·
      refine ⟨181851980073576749013041477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121234653382384499342027651 181851980073576749013041477)
      ·
        refine ⟨34097246263795640439945277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 181851980073576749013041477 34097246263795640439945277)
        ·
          refine ⟨12786467348923365164979479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34097246263795640439945277 12786467348923365164979479)
          ·
            refine ⟨19179701023385047747469219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12786467348923365164979479 19179701023385047747469219)
            ·
              refine ⟨28769551535077571621203829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19179701023385047747469219 28769551535077571621203829)
              ·
                refine ⟨2697145456413522339487859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28769551535077571621203829 2697145456413522339487859)
                ·
                  refine ⟨4045718184620283509231789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2697145456413522339487859 4045718184620283509231789)
                  ·
                    refine ⟨1517144319232606315961921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4045718184620283509231789 1517144319232606315961921)
                    ·
                      refine ⟨1137858239424454736971441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1517144319232606315961921 1137858239424454736971441)
                      ·
                        rfl

theorem cell23_2215971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 5, 1, 3, 2].length) (baseStart_2215971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2215971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2215971 prefixEnd_2215971 := by exact prefixLift 2215971
  have htrace : WordTrace (prefixWord ++ tailWord_2215971) baseStart_2215971 baseEnd_2215971 := by
    simpa [prefixWord, tailWord_2215971, baseEnd_2215971] using wordTrace_append hprefix tailTrace_2215971
  have hstable : (prefixWord ++ tailWord_2215971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2215971).length < 2 ^ (prefixWord ++ tailWord_2215971).sum := by decide
  have hdescent : baseEnd_2215971 < baseStart_2215971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2215971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216007 : List Nat := [1, 1, 4, 1, 3, 1, 2, 1, 9]
def baseStart_2216007 : Nat := 118140960795 + 2216007 * 2 ^ 59
def prefixEnd_2216007 : Nat := 4983230072969 + 3 ^ 40 * 2216007 * 2
def baseEnd_2216007 : Nat := 126430747192001844013475

theorem tailTrace_2216007 : CollatzResearch.WordTrace tailWord_2216007 prefixEnd_2216007 126430747192001844013475 := by
  unfold tailWord_2216007
  simp only [CollatzResearch.WordTrace]
  refine ⟨80824415282792577709662275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53882943521861718473108183 80824415282792577709662275)
  ·
    refine ⟨121236622924188866564493413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80824415282792577709662275 121236622924188866564493413)
    ·
      refine ⟨22731866798285412480842515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 121236622924188866564493413 22731866798285412480842515)
      ·
        refine ⟨34097800197428118721263773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22731866798285412480842515 34097800197428118721263773)
        ·
          refine ⟨12786675074035544520473915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34097800197428118721263773 12786675074035544520473915)
          ·
            refine ⟨19180012611053316780710873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12786675074035544520473915 19180012611053316780710873)
            ·
              refine ⟨14385009458289987585533155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19180012611053316780710873 14385009458289987585533155)
              ·
                refine ⟨21577514187434981378299733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14385009458289987585533155 21577514187434981378299733)
                ·
                  refine ⟨126430747192001844013475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 21577514187434981378299733 126430747192001844013475)
                  ·
                    rfl

theorem cell23_2216007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 9].length) (baseStart_2216007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2216007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2216007 prefixEnd_2216007 := by exact prefixLift 2216007
  have htrace : WordTrace (prefixWord ++ tailWord_2216007) baseStart_2216007 baseEnd_2216007 := by
    simpa [prefixWord, tailWord_2216007, baseEnd_2216007] using wordTrace_append hprefix tailTrace_2216007
  have hstable : (prefixWord ++ tailWord_2216007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216007).length < 2 ^ (prefixWord ++ tailWord_2216007).sum := by decide
  have hdescent : baseEnd_2216007 < baseStart_2216007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216018 : List Nat := [3, 2, 2, 1, 4, 1, 1, 2, 1, 4, 2]
def baseStart_2216018 : Nat := 118140960795 + 2216018 * 2 ^ 59
def prefixEnd_2216018 : Nat := 4983230072969 + 3 ^ 40 * 2216018 * 2
def baseEnd_2216018 : Nat := 1137882373015216053083725

theorem tailTrace_2216018 : CollatzResearch.WordTrace tailWord_2216018 prefixEnd_2216018 1137882373015216053083725 := by
  unfold tailWord_2216018
  simp only [CollatzResearch.WordTrace]
  refine ⟨20206204121438181647078177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53883210990501817725541805 20206204121438181647078177)
  ·
    refine ⟨15154653091078636235308633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20206204121438181647078177 15154653091078636235308633)
    ·
      refine ⟨11365989818308977176481475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15154653091078636235308633 11365989818308977176481475)
      ·
        refine ⟨17048984727463465764722213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11365989818308977176481475 17048984727463465764722213)
        ·
          refine ⟨3196684636399399830885415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17048984727463465764722213 3196684636399399830885415)
          ·
            refine ⟨4795026954599099746328123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3196684636399399830885415 4795026954599099746328123)
            ·
              refine ⟨7192540431898649619492185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4795026954599099746328123 7192540431898649619492185)
              ·
                refine ⟨5394405323923987214619139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7192540431898649619492185 5394405323923987214619139)
                ·
                  refine ⟨8091607985885980821928709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5394405323923987214619139 8091607985885980821928709)
                  ·
                    refine ⟨1517176497353621404111633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8091607985885980821928709 1517176497353621404111633)
                    ·
                      refine ⟨1137882373015216053083725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1517176497353621404111633 1137882373015216053083725)
                      ·
                        rfl

theorem cell23_2216018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 1, 4, 2].length) (baseStart_2216018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2216018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2216018 prefixEnd_2216018 := by exact prefixLift 2216018
  have htrace : WordTrace (prefixWord ++ tailWord_2216018) baseStart_2216018 baseEnd_2216018 := by
    simpa [prefixWord, tailWord_2216018, baseEnd_2216018] using wordTrace_append hprefix tailTrace_2216018
  have hstable : (prefixWord ++ tailWord_2216018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216018).length < 2 ^ (prefixWord ++ tailWord_2216018).sum := by decide
  have hdescent : baseEnd_2216018 < baseStart_2216018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216086 : List Nat := [5, 3, 2, 1, 1, 1, 1, 1, 4, 2, 2]
def baseStart_2216086 : Nat := 118140960795 + 2216086 * 2 ^ 59
def prefixEnd_2216086 : Nat := 4983230072969 + 3 ^ 40 * 2216086 * 2
def baseEnd_2216086 : Nat := 1137917289699721787033413

theorem tailTrace_2216086 : CollatzResearch.WordTrace tailWord_2216086 prefixEnd_2216086 1137917289699721787033413 := by
  unfold tailWord_2216086
  simp only [CollatzResearch.WordTrace]
  refine ⟨5051706040594148387611757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53884864433004249467858741 5051706040594148387611757)
  ·
    refine ⟨1894389765222805645354409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5051706040594148387611757 1894389765222805645354409)
    ·
      refine ⟨1420792323917104234015807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1894389765222805645354409 1420792323917104234015807)
      ·
        refine ⟨2131188485875656351023711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1420792323917104234015807 2131188485875656351023711)
        ·
          refine ⟨3196782728813484526535567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2131188485875656351023711 3196782728813484526535567)
          ·
            refine ⟨4795174093220226789803351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3196782728813484526535567 4795174093220226789803351)
            ·
              refine ⟨7192761139830340184705027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4795174093220226789803351 7192761139830340184705027)
              ·
                refine ⟨10789141709745510277057541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7192761139830340184705027 10789141709745510277057541)
                ·
                  refine ⟨2022964070577283176948289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10789141709745510277057541 2022964070577283176948289)
                  ·
                    refine ⟨1517223052932962382711217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2022964070577283176948289 1517223052932962382711217)
                    ·
                      refine ⟨1137917289699721787033413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1517223052932962382711217 1137917289699721787033413)
                      ·
                        rfl

theorem cell23_2216086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_2216086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2216086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2216086 prefixEnd_2216086 := by exact prefixLift 2216086
  have htrace : WordTrace (prefixWord ++ tailWord_2216086) baseStart_2216086 baseEnd_2216086 := by
    simpa [prefixWord, tailWord_2216086, baseEnd_2216086] using wordTrace_append hprefix tailTrace_2216086
  have hstable : (prefixWord ++ tailWord_2216086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216086).length < 2 ^ (prefixWord ++ tailWord_2216086).sum := by decide
  have hdescent : baseEnd_2216086 < baseStart_2216086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216101 : List Nat := [1, 3, 1, 2, 1, 3, 4, 1, 3, 4]
def baseStart_2216101 : Nat := 118140960795 + 2216101 * 2 ^ 59
def prefixEnd_2216101 : Nat := 4983230072969 + 3 ^ 40 * 2216101 * 2
def baseEnd_2216101 : Nat := 379308330636513076115281

theorem tailTrace_2216101 : CollatzResearch.WordTrace tailWord_2216101 prefixEnd_2216101 379308330636513076115281 := by
  unfold tailWord_2216101
  simp only [CollatzResearch.WordTrace]
  refine ⟨80827843744452031763584157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53885229162968021175722771 80827843744452031763584157)
  ·
    refine ⟨30310441404169511911344059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80827843744452031763584157 30310441404169511911344059)
    ·
      refine ⟨45465662106254267867016089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30310441404169511911344059 45465662106254267867016089)
      ·
        refine ⟨34099246579690700900262067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45465662106254267867016089 34099246579690700900262067)
        ·
          refine ⟨51148869869536051350393101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34099246579690700900262067 51148869869536051350393101)
          ·
            refine ⟨19180826201076019256397413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51148869869536051350393101 19180826201076019256397413)
            ·
              refine ⟨3596404912701753610574515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19180826201076019256397413 3596404912701753610574515)
              ·
                refine ⟨5394607369052630415861773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3596404912701753610574515 5394607369052630415861773)
                ·
                  refine ⟨2022977763394736405948165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5394607369052630415861773 2022977763394736405948165)
                  ·
                    refine ⟨379308330636513076115281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2022977763394736405948165 379308330636513076115281)
                    ·
                      rfl

theorem cell23_2216101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 3, 4].length) (baseStart_2216101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2216101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2216101 prefixEnd_2216101 := by exact prefixLift 2216101
  have htrace : WordTrace (prefixWord ++ tailWord_2216101) baseStart_2216101 baseEnd_2216101 := by
    simpa [prefixWord, tailWord_2216101, baseEnd_2216101] using wordTrace_append hprefix tailTrace_2216101
  have hstable : (prefixWord ++ tailWord_2216101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216101).length < 2 ^ (prefixWord ++ tailWord_2216101).sum := by decide
  have hdescent : baseEnd_2216101 < baseStart_2216101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216107 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 9]
def baseStart_2216107 : Nat := 118140960795 + 2216107 * 2 ^ 59
def prefixEnd_2216107 : Nat := 4983230072969 + 3 ^ 40 * 2216107 * 2
def baseEnd_2216107 : Nat := 1137928072793466204870815

theorem tailTrace_2216107 : CollatzResearch.WordTrace tailWord_2216107 prefixEnd_2216107 1137928072793466204870815 := by
  unfold tailWord_2216107
  simp only [CollatzResearch.WordTrace]
  refine ⟨80828062582430294788302575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53885375054953529858868383 80828062582430294788302575)
  ·
    refine ⟨121242093873645442182453863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80828062582430294788302575 121242093873645442182453863)
    ·
      refine ⟨181863140810468163273680795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121242093873645442182453863 181863140810468163273680795)
      ·
        refine ⟨272794711215702244910521193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181863140810468163273680795 272794711215702244910521193)
        ·
          refine ⟨204596033411776683682890895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 272794711215702244910521193 204596033411776683682890895)
          ·
            refine ⟨306894050117665025524336343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204596033411776683682890895 306894050117665025524336343)
            ·
              refine ⟨460341075176497538286504515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 306894050117665025524336343 460341075176497538286504515)
              ·
                refine ⟨690511612764746307429756773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 460341075176497538286504515 690511612764746307429756773)
                ·
                  refine ⟨129470927393389932643079395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 690511612764746307429756773 129470927393389932643079395)
                  ·
                    refine ⟨194206391090084898964619093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 129470927393389932643079395 194206391090084898964619093)
                    ·
                      refine ⟨1137928072793466204870815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 194206391090084898964619093 1137928072793466204870815)
                      ·
                        rfl

theorem cell23_2216107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 9].length) (baseStart_2216107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2216107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2216107 prefixEnd_2216107 := by exact prefixLift 2216107
  have htrace : WordTrace (prefixWord ++ tailWord_2216107) baseStart_2216107 baseEnd_2216107 := by
    simpa [prefixWord, tailWord_2216107, baseEnd_2216107] using wordTrace_append hprefix tailTrace_2216107
  have hstable : (prefixWord ++ tailWord_2216107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216107).length < 2 ^ (prefixWord ++ tailWord_2216107).sum := by decide
  have hdescent : baseEnd_2216107 < baseStart_2216107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216164 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 2, 5, 4]
def baseStart_2216164 : Nat := 118140960795 + 2216164 * 2 ^ 59
def prefixEnd_2216164 : Nat := 4983230072969 + 3 ^ 40 * 2216164 * 2
def baseEnd_2216164 : Nat := 1137957341190772481858053

theorem tailTrace_2216164 : CollatzResearch.WordTrace tailWord_2216164 prefixEnd_2216164 1137957341190772481858053 := by
  unfold tailWord_2216164
  simp only [CollatzResearch.WordTrace]
  refine ⟨40415070771611896761563773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53886761028815862348751697 40415070771611896761563773)
  ·
    refine ⟨15155651539354461285586415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40415070771611896761563773 15155651539354461285586415)
    ·
      refine ⟨22733477309031691928379623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15155651539354461285586415 22733477309031691928379623)
      ·
        refine ⟨34100215963547537892569435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22733477309031691928379623 34100215963547537892569435)
        ·
          refine ⟨51150323945321306838854153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34100215963547537892569435 51150323945321306838854153)
          ·
            refine ⟨38362742958990980129140615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51150323945321306838854153 38362742958990980129140615)
            ·
              refine ⟨57544114438486470193710923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38362742958990980129140615 57544114438486470193710923)
              ·
                refine ⟨86316171657729705290566385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57544114438486470193710923 86316171657729705290566385)
                ·
                  refine ⟨64737128743297278967924789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86316171657729705290566385 64737128743297278967924789)
                  ·
                    refine ⟨6069105819684119903242949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 64737128743297278967924789 6069105819684119903242949)
                    ·
                      refine ⟨1137957341190772481858053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6069105819684119903242949 1137957341190772481858053)
                      ·
                        rfl

theorem cell23_2216164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_2216164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2216164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2216164 prefixEnd_2216164 := by exact prefixLift 2216164
  have htrace : WordTrace (prefixWord ++ tailWord_2216164) baseStart_2216164 baseEnd_2216164 := by
    simpa [prefixWord, tailWord_2216164, baseEnd_2216164] using wordTrace_append hprefix tailTrace_2216164
  have hstable : (prefixWord ++ tailWord_2216164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216164).length < 2 ^ (prefixWord ++ tailWord_2216164).sum := by decide
  have hdescent : baseEnd_2216164 < baseStart_2216164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216178 : List Nat := [3, 2, 1, 3, 2, 1, 3, 2, 1, 5]
def baseStart_2216178 : Nat := 118140960795 + 2216178 * 2 ^ 59
def prefixEnd_2216178 : Nat := 4983230072969 + 3 ^ 40 * 2216178 * 2
def baseEnd_2216178 : Nat := 379321509973311809027663

theorem tailTrace_2216178 : CollatzResearch.WordTrace tailWord_2216178 prefixEnd_2216178 379321509973311809027663 := by
  unfold tailWord_2216178
  simp only [CollatzResearch.WordTrace]
  refine ⟨20207663041293268478534297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53887101443448715942758125 20207663041293268478534297)
  ·
    refine ⟨15155747280969951358900723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20207663041293268478534297 15155747280969951358900723)
    ·
      refine ⟨22733620921454927038351085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15155747280969951358900723 22733620921454927038351085)
      ·
        refine ⟨8525107845545597639381657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22733620921454927038351085 8525107845545597639381657)
        ·
          refine ⟨6393830884159198229536243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8525107845545597639381657 6393830884159198229536243)
          ·
            refine ⟨9590746326238797344304365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6393830884159198229536243 9590746326238797344304365)
            ·
              refine ⟨3596529872339549004114137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9590746326238797344304365 3596529872339549004114137)
              ·
                refine ⟨2697397404254661753085603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3596529872339549004114137 2697397404254661753085603)
                ·
                  refine ⟨4046096106381992629628405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2697397404254661753085603 4046096106381992629628405)
                  ·
                    refine ⟨379321509973311809027663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4046096106381992629628405 379321509973311809027663)
                    ·
                      rfl

theorem cell23_2216178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 2, 1, 5].length) (baseStart_2216178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2216178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2216178 prefixEnd_2216178 := by exact prefixLift 2216178
  have htrace : WordTrace (prefixWord ++ tailWord_2216178) baseStart_2216178 baseEnd_2216178 := by
    simpa [prefixWord, tailWord_2216178, baseEnd_2216178] using wordTrace_append hprefix tailTrace_2216178
  have hstable : (prefixWord ++ tailWord_2216178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216178).length < 2 ^ (prefixWord ++ tailWord_2216178).sum := by decide
  have hdescent : baseEnd_2216178 < baseStart_2216178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216184 : List Nat := [2, 1, 2, 1, 1, 2, 1, 4, 3, 1, 5]
def baseStart_2216184 : Nat := 118140960795 + 2216184 * 2 ^ 59
def prefixEnd_2216184 : Nat := 4983230072969 + 3 ^ 40 * 2216184 * 2
def baseEnd_2216184 : Nat := 1137967610803862403607961

theorem tailTrace_2216184 : CollatzResearch.WordTrace tailWord_2216184 prefixEnd_2216184 1137967610803862403607961 := by
  unfold tailWord_2216184
  simp only [CollatzResearch.WordTrace]
  refine ⟨40415435501575668469427803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53887247335434224625903737 40415435501575668469427803)
  ·
    refine ⟨60623153252363502704141705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40415435501575668469427803 60623153252363502704141705)
    ·
      refine ⟨45467364939272627028106279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60623153252363502704141705 45467364939272627028106279)
      ·
        refine ⟨68201047408908940542159419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45467364939272627028106279 68201047408908940542159419)
        ·
          refine ⟨102301571113363410813239129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68201047408908940542159419 102301571113363410813239129)
          ·
            refine ⟨76726178335022558109929347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102301571113363410813239129 76726178335022558109929347)
            ·
              refine ⟨115089267502533837164894021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76726178335022558109929347 115089267502533837164894021)
              ·
                refine ⟨21579237656725094468417629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 115089267502533837164894021 21579237656725094468417629)
                ·
                  refine ⟨8092214121271910425656611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21579237656725094468417629 8092214121271910425656611)
                  ·
                    refine ⟨12138321181907865638484917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8092214121271910425656611 12138321181907865638484917)
                    ·
                      refine ⟨1137967610803862403607961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12138321181907865638484917 1137967610803862403607961)
                      ·
                        rfl

theorem cell23_2216184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 3, 1, 5].length) (baseStart_2216184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2216184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2216184 prefixEnd_2216184 := by exact prefixLift 2216184
  have htrace : WordTrace (prefixWord ++ tailWord_2216184) baseStart_2216184 baseEnd_2216184 := by
    simpa [prefixWord, tailWord_2216184, baseEnd_2216184] using wordTrace_append hprefix tailTrace_2216184
  have hstable : (prefixWord ++ tailWord_2216184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216184).length < 2 ^ (prefixWord ++ tailWord_2216184).sum := by decide
  have hdescent : baseEnd_2216184 < baseStart_2216184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216201 : List Nat := [1, 2, 1, 1, 3, 4, 3, 1, 1, 1, 5]
def baseStart_2216201 : Nat := 118140960795 + 2216201 * 2 ^ 59
def prefixEnd_2216201 : Nat := 4983230072969 + 3 ^ 40 * 2216201 * 2
def baseEnd_2216201 : Nat := 1137976339974988837095383

theorem tailTrace_2216201 : CollatzResearch.WordTrace tailWord_2216201 prefixEnd_2216201 1137976339974988837095383 := by
  unfold tailWord_2216201
  simp only [CollatzResearch.WordTrace]
  refine ⟨80831491044089748842224457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53887660696059832561482971 80831491044089748842224457)
  ·
    refine ⟨60623618283067311631668343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80831491044089748842224457 60623618283067311631668343)
    ·
      refine ⟨90935427424600967447502515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60623618283067311631668343 90935427424600967447502515)
      ·
        refine ⟨136403141136901451171253773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90935427424600967447502515 136403141136901451171253773)
        ·
          refine ⟨51151177926338044189220165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136403141136901451171253773 51151177926338044189220165)
          ·
            refine ⟨9590845861188383285478781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51151177926338044189220165 9590845861188383285478781)
            ·
              refine ⟨3596567197945643732054543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9590845861188383285478781 3596567197945643732054543)
              ·
                refine ⟨5394850796918465598081815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3596567197945643732054543 5394850796918465598081815)
                ·
                  refine ⟨8092276195377698397122723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5394850796918465598081815 8092276195377698397122723)
                  ·
                    refine ⟨12138414293066547595684085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8092276195377698397122723 12138414293066547595684085)
                    ·
                      refine ⟨1137976339974988837095383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12138414293066547595684085 1137976339974988837095383)
                      ·
                        rfl

theorem cell23_2216201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 1, 5].length) (baseStart_2216201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2216201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2216201 prefixEnd_2216201 := by exact prefixLift 2216201
  have htrace : WordTrace (prefixWord ++ tailWord_2216201) baseStart_2216201 baseEnd_2216201 := by
    simpa [prefixWord, tailWord_2216201, baseEnd_2216201] using wordTrace_append hprefix tailTrace_2216201
  have hstable : (prefixWord ++ tailWord_2216201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216201).length < 2 ^ (prefixWord ++ tailWord_2216201).sum := by decide
  have hdescent : baseEnd_2216201 < baseStart_2216201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216228 : List Nat := [2, 3, 1, 3, 1, 3, 2, 1, 1, 2, 4]
def baseStart_2216228 : Nat := 118140960795 + 2216228 * 2 ^ 59
def prefixEnd_2216228 : Nat := 4983230072969 + 3 ^ 40 * 2216228 * 2
def baseEnd_2216228 : Nat := 1137990203952660231457759

theorem tailTrace_2216228 : CollatzResearch.WordTrace tailWord_2216228 prefixEnd_2216228 1137990203952660231457759 := by
  unfold tailWord_2216228
  simp only [CollatzResearch.WordTrace]
  refine ⟨40416237907495966226728669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53888317209994621635638225 40416237907495966226728669)
  ·
    refine ⟨15156089215310987335023251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40416237907495966226728669 15156089215310987335023251)
    ·
      refine ⟨22734133822966481002534877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15156089215310987335023251 22734133822966481002534877)
      ·
        refine ⟨8525300183612430375950579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22734133822966481002534877 8525300183612430375950579)
        ·
          refine ⟨12787950275418645563925869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8525300183612430375950579 12787950275418645563925869)
          ·
            refine ⟨4795481353281992086472201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12787950275418645563925869 4795481353281992086472201)
            ·
              refine ⟨3596611014961494064854151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4795481353281992086472201 3596611014961494064854151)
              ·
                refine ⟨5394916522442241097281227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3596611014961494064854151 5394916522442241097281227)
                ·
                  refine ⟨8092374783663361645921841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5394916522442241097281227 8092374783663361645921841)
                  ·
                    refine ⟨6069281087747521234441381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8092374783663361645921841 6069281087747521234441381)
                    ·
                      refine ⟨1137990203952660231457759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6069281087747521234441381 1137990203952660231457759)
                      ·
                        rfl

theorem cell23_2216228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_2216228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2216228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2216228 prefixEnd_2216228 := by exact prefixLift 2216228
  have htrace : WordTrace (prefixWord ++ tailWord_2216228) baseStart_2216228 baseEnd_2216228 := by
    simpa [prefixWord, tailWord_2216228, baseEnd_2216228] using wordTrace_append hprefix tailTrace_2216228
  have hstable : (prefixWord ++ tailWord_2216228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216228).length < 2 ^ (prefixWord ++ tailWord_2216228).sum := by decide
  have hdescent : baseEnd_2216228 < baseStart_2216228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216232 : List Nat := [2, 1, 5, 1, 3, 1, 1, 2, 3, 2, 2]
def baseStart_2216232 : Nat := 118140960795 + 2216232 * 2 ^ 59
def prefixEnd_2216232 : Nat := 4983230072969 + 3 ^ 40 * 2216232 * 2
def baseEnd_2216232 : Nat := 1137992257875278215807741

theorem tailTrace_2216232 : CollatzResearch.WordTrace tailWord_2216232 prefixEnd_2216232 1137992257875278215807741 := by
  unfold tailWord_2216232
  simp only [CollatzResearch.WordTrace]
  refine ⟨40416310853488720568301475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53888414471318294091068633 40416310853488720568301475)
  ·
    refine ⟨60624466280233080852452213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40416310853488720568301475 60624466280233080852452213)
    ·
      refine ⟨5683543713771851329917395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60624466280233080852452213 5683543713771851329917395)
      ·
        refine ⟨8525315570657776994876093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5683543713771851329917395 8525315570657776994876093)
        ·
          refine ⟨3196993338996666373078535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8525315570657776994876093 3196993338996666373078535)
          ·
            refine ⟨4795490008494999559617803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3196993338996666373078535 4795490008494999559617803)
            ·
              refine ⟨7193235012742499339426705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4795490008494999559617803 7193235012742499339426705)
              ·
                refine ⟨5394926259556874504570029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7193235012742499339426705 5394926259556874504570029)
                ·
                  refine ⟨2023097347333827939213761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5394926259556874504570029 2023097347333827939213761)
                  ·
                    refine ⟨1517323010500370954410321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2023097347333827939213761 1517323010500370954410321)
                    ·
                      refine ⟨1137992257875278215807741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1517323010500370954410321 1137992257875278215807741)
                      ·
                        rfl

theorem cell23_2216232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_2216232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2216232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2216232 prefixEnd_2216232 := by exact prefixLift 2216232
  have htrace : WordTrace (prefixWord ++ tailWord_2216232) baseStart_2216232 baseEnd_2216232 := by
    simpa [prefixWord, tailWord_2216232, baseEnd_2216232] using wordTrace_append hprefix tailTrace_2216232
  have hstable : (prefixWord ++ tailWord_2216232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216232).length < 2 ^ (prefixWord ++ tailWord_2216232).sum := by decide
  have hdescent : baseEnd_2216232 < baseStart_2216232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216249 : List Nat := [1, 2, 1, 6, 1, 2, 2, 3, 1, 2, 2]
def baseStart_2216249 : Nat := 118140960795 + 2216249 * 2 ^ 59
def prefixEnd_2216249 : Nat := 4983230072969 + 3 ^ 40 * 2216249 * 2
def baseEnd_2216249 : Nat := 1138000987046404649295163

theorem tailTrace_2216249 : CollatzResearch.WordTrace tailWord_2216249 prefixEnd_2216249 1138000987046404649295163 := by
  unfold tailWord_2216249
  simp only [CollatzResearch.WordTrace]
  refine ⟨80833241747915853039971801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53888827831943902026647867 80833241747915853039971801)
  ·
    refine ⟨60624931310936889779978851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80833241747915853039971801 60624931310936889779978851)
    ·
      refine ⟨90937396966405334669968277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60624931310936889779978851 90937396966405334669968277)
      ·
        refine ⟨4262690482800250062654763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 90937396966405334669968277 4262690482800250062654763)
        ·
          refine ⟨6394035724200375093982145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4262690482800250062654763 6394035724200375093982145)
          ·
            refine ⟨4795526793150281320486609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6394035724200375093982145 4795526793150281320486609)
            ·
              refine ⟨3596645094862710990364957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4795526793150281320486609 3596645094862710990364957)
              ·
                refine ⟨1348741910573516621386859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3596645094862710990364957 1348741910573516621386859)
                ·
                  refine ⟨2023112865860274932080289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1348741910573516621386859 2023112865860274932080289)
                  ·
                    refine ⟨1517334649395206199060217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2023112865860274932080289 1517334649395206199060217)
                    ·
                      refine ⟨1138000987046404649295163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1517334649395206199060217 1138000987046404649295163)
                      ·
                        rfl

theorem cell23_2216249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_2216249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2216249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2216249 prefixEnd_2216249 := by exact prefixLift 2216249
  have htrace : WordTrace (prefixWord ++ tailWord_2216249) baseStart_2216249 baseEnd_2216249 := by
    simpa [prefixWord, tailWord_2216249, baseEnd_2216249] using wordTrace_append hprefix tailTrace_2216249
  have hstable : (prefixWord ++ tailWord_2216249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216249).length < 2 ^ (prefixWord ++ tailWord_2216249).sum := by decide
  have hdescent : baseEnd_2216249 < baseStart_2216249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216291 : List Nat := [1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 5]
def baseStart_2216291 : Nat := 118140960795 + 2216291 * 2 ^ 59
def prefixEnd_2216291 : Nat := 4983230072969 + 3 ^ 40 * 2216291 * 2
def baseEnd_2216291 : Nat := 1138022553233893484969969

theorem tailTrace_2216291 : CollatzResearch.WordTrace tailWord_2216291 prefixEnd_2216291 1138022553233893484969969 := by
  unfold tailWord_2216291
  simp only [CollatzResearch.WordTrace]
  refine ⟨80834773613763694213000727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53889849075842462808667151 80834773613763694213000727)
  ·
    refine ⟨121252160420645541319501091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80834773613763694213000727 121252160420645541319501091)
    ·
      refine ⟨181878240630968311979251637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121252160420645541319501091 181878240630968311979251637)
      ·
        refine ⟨17051085059153279248054841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 181878240630968311979251637 17051085059153279248054841)
        ·
          refine ⟨12788313794364959436041131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17051085059153279248054841 12788313794364959436041131)
          ·
            refine ⟨19182470691547439154061697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12788313794364959436041131 19182470691547439154061697)
            ·
              refine ⟨14386853018660579365546273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19182470691547439154061697 14386853018660579365546273)
              ·
                refine ⟨10790139763995434524159705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14386853018660579365546273 10790139763995434524159705)
                ·
                  refine ⟨8092604822996575893119779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10790139763995434524159705 8092604822996575893119779)
                  ·
                    refine ⟨12138907234494863839679669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8092604822996575893119779 12138907234494863839679669)
                    ·
                      refine ⟨1138022553233893484969969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12138907234494863839679669 1138022553233893484969969)
                      ·
                        rfl

theorem cell23_2216291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_2216291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2216291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2216291 prefixEnd_2216291 := by exact prefixLift 2216291
  have htrace : WordTrace (prefixWord ++ tailWord_2216291) baseStart_2216291 baseEnd_2216291 := by
    simpa [prefixWord, tailWord_2216291, baseEnd_2216291] using wordTrace_append hprefix tailTrace_2216291
  have hstable : (prefixWord ++ tailWord_2216291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216291).length < 2 ^ (prefixWord ++ tailWord_2216291).sum := by decide
  have hdescent : baseEnd_2216291 < baseStart_2216291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216341 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 6, 5]
def baseStart_2216341 : Nat := 118140960795 + 2216341 * 2 ^ 59
def prefixEnd_2216341 : Nat := 4983230072969 + 3 ^ 40 * 2216341 * 2
def baseEnd_2216341 : Nat := 379349409088872763114913

theorem tailTrace_2216341 : CollatzResearch.WordTrace tailWord_2216341 prefixEnd_2216341 379349409088872763114913 := by
  unfold tailWord_2216341
  simp only [CollatzResearch.WordTrace]
  refine ⟨80836597263582552752320877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53891064842388368501547251 80836597263582552752320877)
  ·
    refine ⟨30313723973843457282120329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80836597263582552752320877 30313723973843457282120329)
    ·
      refine ⟨22735292980382592961590247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30313723973843457282120329 22735292980382592961590247)
      ·
        refine ⟨34102939470573889442385371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22735292980382592961590247 34102939470573889442385371)
        ·
          refine ⟨51154409205860834163578057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34102939470573889442385371 51154409205860834163578057)
          ·
            refine ⟨38365806904395625622683543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51154409205860834163578057 38365806904395625622683543)
            ·
              refine ⟨57548710356593438434025315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38365806904395625622683543 57548710356593438434025315)
              ·
                refine ⟨86323065534890157651037973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57548710356593438434025315 86323065534890157651037973)
                ·
                  refine ⟨4046393696947976139892405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 86323065534890157651037973 4046393696947976139892405)
                  ·
                    refine ⟨379349409088872763114913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4046393696947976139892405 379349409088872763114913)
                    ·
                      rfl

theorem cell23_2216341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 6, 5].length) (baseStart_2216341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2216341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2216341 prefixEnd_2216341 := by exact prefixLift 2216341
  have htrace : WordTrace (prefixWord ++ tailWord_2216341) baseStart_2216341 baseEnd_2216341 := by
    simpa [prefixWord, tailWord_2216341, baseEnd_2216341] using wordTrace_append hprefix tailTrace_2216341
  have hstable : (prefixWord ++ tailWord_2216341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216341).length < 2 ^ (prefixWord ++ tailWord_2216341).sum := by decide
  have hdescent : baseEnd_2216341 < baseStart_2216341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216351 : List Nat := [1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 7]
def baseStart_2216351 : Nat := 118140960795 + 2216351 * 2 ^ 59
def prefixEnd_2216351 : Nat := 4983230072969 + 3 ^ 40 * 2216351 * 2
def baseEnd_2216351 : Nat := 1138053362073163250219693

theorem tailTrace_2216351 : CollatzResearch.WordTrace tailWord_2216351 prefixEnd_2216351 1138053362073163250219693 := by
  unfold tailWord_2216351
  simp only [CollatzResearch.WordTrace]
  refine ⟨80836961993546324460184907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53891307995697549640123271 80836961993546324460184907)
  ·
    refine ⟨121255442990319486690277361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80836961993546324460184907 121255442990319486690277361)
    ·
      refine ⟨90941582242739615017708021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121255442990319486690277361 90941582242739615017708021)
      ·
        refine ⟨8525773335256838907910127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 90941582242739615017708021 8525773335256838907910127)
        ·
          refine ⟨12788660002885258361865191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8525773335256838907910127 12788660002885258361865191)
          ·
            refine ⟨19182990004327887542797787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12788660002885258361865191 19182990004327887542797787)
            ·
              refine ⟨28774485006491831314196681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19182990004327887542797787 28774485006491831314196681)
              ·
                refine ⟨21580863754868873485647511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28774485006491831314196681 21580863754868873485647511)
                ·
                  refine ⟨32371295632303310228471267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21580863754868873485647511 32371295632303310228471267)
                  ·
                    refine ⟨48556943448454965342706901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32371295632303310228471267 48556943448454965342706901)
                    ·
                      refine ⟨1138053362073163250219693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 48556943448454965342706901 1138053362073163250219693)
                      ·
                        rfl

theorem cell23_2216351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_2216351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2216351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2216351 prefixEnd_2216351 := by exact prefixLift 2216351
  have htrace : WordTrace (prefixWord ++ tailWord_2216351) baseStart_2216351 baseEnd_2216351 := by
    simpa [prefixWord, tailWord_2216351, baseEnd_2216351] using wordTrace_append hprefix tailTrace_2216351
  have hstable : (prefixWord ++ tailWord_2216351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216351).length < 2 ^ (prefixWord ++ tailWord_2216351).sum := by decide
  have hdescent : baseEnd_2216351 < baseStart_2216351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216361 : List Nat := [1, 2, 1, 1, 1, 1, 3, 5, 1, 3, 4]
def baseStart_2216361 : Nat := 118140960795 + 2216361 * 2 ^ 59
def prefixEnd_2216361 : Nat := 4983230072969 + 3 ^ 40 * 2216361 * 2
def baseEnd_2216361 : Nat := 1138058496879708211094647

theorem tailTrace_2216361 : CollatzResearch.WordTrace tailWord_2216361 prefixEnd_2216361 1138058496879708211094647 := by
  unfold tailWord_2216361
  simp only [CollatzResearch.WordTrace]
  refine ⟨80837326723510096168048937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53891551149006730778699291 80837326723510096168048937)
  ·
    refine ⟨60627995042632572126036703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80837326723510096168048937 60627995042632572126036703)
    ·
      refine ⟨90941992563948858189055055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60627995042632572126036703 90941992563948858189055055)
      ·
        refine ⟨136412988845923287283582583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90941992563948858189055055 136412988845923287283582583)
        ·
          refine ⟨204619483268884930925373875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136412988845923287283582583 204619483268884930925373875)
          ·
            refine ⟨306929224903327396388060813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204619483268884930925373875 306929224903327396388060813)
            ·
              refine ⟨115098459338747773645522805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 306929224903327396388060813 115098459338747773645522805)
              ·
                refine ⟨10790480563007603779267763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 115098459338747773645522805 10790480563007603779267763)
                ·
                  refine ⟨16185720844511405668901645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10790480563007603779267763 16185720844511405668901645)
                  ·
                    refine ⟨6069645316691777125838117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16185720844511405668901645 6069645316691777125838117)
                    ·
                      refine ⟨1138058496879708211094647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6069645316691777125838117 1138058496879708211094647)
                      ·
                        rfl

theorem cell23_2216361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 3, 4].length) (baseStart_2216361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2216361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2216361 prefixEnd_2216361 := by exact prefixLift 2216361
  have htrace : WordTrace (prefixWord ++ tailWord_2216361) baseStart_2216361 baseEnd_2216361 := by
    simpa [prefixWord, tailWord_2216361, baseEnd_2216361] using wordTrace_append hprefix tailTrace_2216361
  have hstable : (prefixWord ++ tailWord_2216361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216361).length < 2 ^ (prefixWord ++ tailWord_2216361).sum := by decide
  have hdescent : baseEnd_2216361 < baseStart_2216361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216378 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 3, 6, 2]
def baseStart_2216378 : Nat := 118140960795 + 2216378 * 2 ^ 59
def prefixEnd_2216378 : Nat := 4983230072969 + 3 ^ 40 * 2216378 * 2
def baseEnd_2216378 : Nat := 1138067226050834644582069

theorem tailTrace_2216378 : CollatzResearch.WordTrace tailWord_2216378 prefixEnd_2216378 1138067226050834644582069 := by
  unfold tailWord_2216378
  simp only [CollatzResearch.WordTrace]
  refine ⟨20209486691112127017854447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53891964509632338714278525 20209486691112127017854447)
  ·
    refine ⟨30314230036668190526781671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20209486691112127017854447 30314230036668190526781671)
    ·
      refine ⟨45471345055002285790172507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30314230036668190526781671 45471345055002285790172507)
      ·
        refine ⟨68207017582503428685258761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45471345055002285790172507 68207017582503428685258761)
        ·
          refine ⟨51155263186877571513944071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68207017582503428685258761 51155263186877571513944071)
          ·
            refine ⟨76732894780316357270916107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51155263186877571513944071 76732894780316357270916107)
            ·
              refine ⟨115099342170474535906374161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76732894780316357270916107 115099342170474535906374161)
              ·
                refine ⟨86324506627855901929780621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115099342170474535906374161 86324506627855901929780621)
                ·
                  refine ⟨32371689985445963223667733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86324506627855901929780621 32371689985445963223667733)
                  ·
                    refine ⟨1517422968067779526109425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 32371689985445963223667733 1517422968067779526109425)
                    ·
                      refine ⟨1138067226050834644582069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1517422968067779526109425 1138067226050834644582069)
                      ·
                        rfl

theorem cell23_2216378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 3, 6, 2].length) (baseStart_2216378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2216378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2216378 prefixEnd_2216378 := by exact prefixLift 2216378
  have htrace : WordTrace (prefixWord ++ tailWord_2216378) baseStart_2216378 baseEnd_2216378 := by
    simpa [prefixWord, tailWord_2216378, baseEnd_2216378] using wordTrace_append hprefix tailTrace_2216378
  have hstable : (prefixWord ++ tailWord_2216378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216378).length < 2 ^ (prefixWord ++ tailWord_2216378).sum := by decide
  have hdescent : baseEnd_2216378 < baseStart_2216378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216398 : List Nat := [4, 1, 1, 1, 2, 1, 1, 4, 1, 4, 3]
def baseStart_2216398 : Nat := 118140960795 + 2216398 * 2 ^ 59
def prefixEnd_2216398 : Nat := 4983230072969 + 3 ^ 40 * 2216398 * 2
def baseEnd_2216398 : Nat := 1138077495663924566331977

theorem tailTrace_2216398 : CollatzResearch.WordTrace tailWord_2216398 prefixEnd_2216398 1138077495663924566331977 := by
  unfold tailWord_2216398
  simp only [CollatzResearch.WordTrace]
  refine ⟨10104834528047006435893231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53892450816250700991430565 10104834528047006435893231)
  ·
    refine ⟨15157251792070509653839847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10104834528047006435893231 15157251792070509653839847)
    ·
      refine ⟨22735877688105764480759771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15157251792070509653839847 22735877688105764480759771)
      ·
        refine ⟨34103816532158646721139657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22735877688105764480759771 34103816532158646721139657)
        ·
          refine ⟨25577862399118985040854743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34103816532158646721139657 25577862399118985040854743)
          ·
            refine ⟨38366793598678477561282115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25577862399118985040854743 38366793598678477561282115)
            ·
              refine ⟨57550190398017716341923173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38366793598678477561282115 57550190398017716341923173)
              ·
                refine ⟨10790660699628321814110595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57550190398017716341923173 10790660699628321814110595)
                ·
                  refine ⟨16185991049442482721165893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10790660699628321814110595 16185991049442482721165893)
                  ·
                    refine ⟨3034873321770465510218605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16185991049442482721165893 3034873321770465510218605)
                    ·
                      refine ⟨1138077495663924566331977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3034873321770465510218605 1138077495663924566331977)
                      ·
                        rfl

theorem cell23_2216398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 1, 4, 3].length) (baseStart_2216398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2216398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2216398 prefixEnd_2216398 := by exact prefixLift 2216398
  have htrace : WordTrace (prefixWord ++ tailWord_2216398) baseStart_2216398 baseEnd_2216398 := by
    simpa [prefixWord, tailWord_2216398, baseEnd_2216398] using wordTrace_append hprefix tailTrace_2216398
  have hstable : (prefixWord ++ tailWord_2216398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216398).length < 2 ^ (prefixWord ++ tailWord_2216398).sum := by decide
  have hdescent : baseEnd_2216398 < baseStart_2216398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216405 : List Nat := [1, 3, 2, 3, 1, 3, 1, 2, 3, 4]
def baseStart_2216405 : Nat := 118140960795 + 2216405 * 2 ^ 59
def prefixEnd_2216405 : Nat := 4983230072969 + 3 ^ 40 * 2216405 * 2
def baseEnd_2216405 : Nat := 379360363342835346314815

theorem tailTrace_2216405 : CollatzResearch.WordTrace tailWord_2216405 prefixEnd_2216405 379360363342835346314815 := by
  unfold tailWord_2216405
  simp only [CollatzResearch.WordTrace]
  refine ⟨80838931535350691682650669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53892621023567127788433779 80838931535350691682650669)
  ·
    refine ⟨30314599325756509380994001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80838931535350691682650669 30314599325756509380994001)
    ·
      refine ⟨22735949494317382035745501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30314599325756509380994001 22735949494317382035745501)
      ·
        refine ⟨8525981060369018263404563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22735949494317382035745501 8525981060369018263404563)
        ·
          refine ⟨12788971590553527395106845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8525981060369018263404563 12788971590553527395106845)
          ·
            refine ⟨4795864346457572773165067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12788971590553527395106845 4795864346457572773165067)
            ·
              refine ⟨7193796519686359159747601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4795864346457572773165067 7193796519686359159747601)
              ·
                refine ⟨5395347389764769369810701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7193796519686359159747601 5395347389764769369810701)
                ·
                  refine ⟨2023255271161788513679013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5395347389764769369810701 2023255271161788513679013)
                  ·
                    refine ⟨379360363342835346314815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2023255271161788513679013 379360363342835346314815)
                    ·
                      rfl

theorem cell23_2216405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 3, 4].length) (baseStart_2216405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2216405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2216405 prefixEnd_2216405 := by exact prefixLift 2216405
  have htrace : WordTrace (prefixWord ++ tailWord_2216405) baseStart_2216405 baseEnd_2216405 := by
    simpa [prefixWord, tailWord_2216405, baseEnd_2216405] using wordTrace_append hprefix tailTrace_2216405
  have hstable : (prefixWord ++ tailWord_2216405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216405).length < 2 ^ (prefixWord ++ tailWord_2216405).sum := by decide
  have hdescent : baseEnd_2216405 < baseStart_2216405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216415 : List Nat := [1, 1, 2, 3, 3, 2, 3, 1, 2, 2, 3]
def baseStart_2216415 : Nat := 118140960795 + 2216415 * 2 ^ 59
def prefixEnd_2216415 : Nat := 4983230072969 + 3 ^ 40 * 2216415 * 2
def baseEnd_2216415 : Nat := 1138086224835050999819399

theorem tailTrace_2216415 : CollatzResearch.WordTrace tailWord_2216415 prefixEnd_2216415 1138086224835050999819399 := by
  unfold tailWord_2216415
  simp only [CollatzResearch.WordTrace]
  refine ⟨80839296265314463390514699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53892864176876308927009799 80839296265314463390514699)
  ·
    refine ⟨121258944397971695085772049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80839296265314463390514699 121258944397971695085772049)
    ·
      refine ⟨90944208298478771314329037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121258944397971695085772049 90944208298478771314329037)
      ·
        refine ⟨34104078111929539242873389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90944208298478771314329037 34104078111929539242873389)
        ·
          refine ⟨12789029291973577216077521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34104078111929539242873389 12789029291973577216077521)
          ·
            refine ⟨9591771968980182912058141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12789029291973577216077521 9591771968980182912058141)
            ·
              refine ⟨3596914488367568592021803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9591771968980182912058141 3596914488367568592021803)
              ·
                refine ⟨5395371732551352888032705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3596914488367568592021803 5395371732551352888032705)
                ·
                  refine ⟨4046528799413514666024529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5395371732551352888032705 4046528799413514666024529)
                  ·
                    refine ⟨3034896599560135999518397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4046528799413514666024529 3034896599560135999518397)
                    ·
                      refine ⟨1138086224835050999819399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3034896599560135999518397 1138086224835050999819399)
                      ·
                        rfl

theorem cell23_2216415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 2, 2, 3].length) (baseStart_2216415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2216415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2216415 prefixEnd_2216415 := by exact prefixLift 2216415
  have htrace : WordTrace (prefixWord ++ tailWord_2216415) baseStart_2216415 baseEnd_2216415 := by
    simpa [prefixWord, tailWord_2216415, baseEnd_2216415] using wordTrace_append hprefix tailTrace_2216415
  have hstable : (prefixWord ++ tailWord_2216415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216415).length < 2 ^ (prefixWord ++ tailWord_2216415).sum := by decide
  have hdescent : baseEnd_2216415 < baseStart_2216415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216438 : List Nat := [5, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8]
def baseStart_2216438 : Nat := 118140960795 + 2216438 * 2 ^ 59
def prefixEnd_2216438 : Nat := 4983230072969 + 3 ^ 40 * 2216438 * 2
def baseEnd_2216438 : Nat := 1138098034890104409831793

theorem tailTrace_2216438 : CollatzResearch.WordTrace tailWord_2216438 prefixEnd_2216438 1138098034890104409831793 := by
  unfold tailWord_2216438
  simp only [CollatzResearch.WordTrace]
  refine ⟨5052508446514446144912623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53893423429487425545734645 5052508446514446144912623)
  ·
    refine ⟨7578762669771669217368935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5052508446514446144912623 7578762669771669217368935)
    ·
      refine ⟨11368144004657503826053403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7578762669771669217368935 11368144004657503826053403)
      ·
        refine ⟨17052216006986255739080105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11368144004657503826053403 17052216006986255739080105)
        ·
          refine ⟨12789162005239691804310079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17052216006986255739080105 12789162005239691804310079)
          ·
            refine ⟨19183743007859537706465119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12789162005239691804310079 19183743007859537706465119)
            ·
              refine ⟨28775614511789306559697679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19183743007859537706465119 28775614511789306559697679)
              ·
                refine ⟨43163421767683959839546519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28775614511789306559697679 43163421767683959839546519)
                ·
                  refine ⟨64745132651525939759319779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43163421767683959839546519 64745132651525939759319779)
                  ·
                    refine ⟨97117698977288909638979669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 64745132651525939759319779 97117698977288909638979669)
                    ·
                      refine ⟨1138098034890104409831793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 97117698977288909638979669 1138098034890104409831793)
                      ·
                        rfl

theorem cell23_2216438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_2216438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2216438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2216438 prefixEnd_2216438 := by exact prefixLift 2216438
  have htrace : WordTrace (prefixWord ++ tailWord_2216438) baseStart_2216438 baseEnd_2216438 := by
    simpa [prefixWord, tailWord_2216438, baseEnd_2216438] using wordTrace_append hprefix tailTrace_2216438
  have hstable : (prefixWord ++ tailWord_2216438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216438).length < 2 ^ (prefixWord ++ tailWord_2216438).sum := by decide
  have hdescent : baseEnd_2216438 < baseStart_2216438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216452 : List Nat := [2, 3, 2, 3, 1, 2, 3, 1, 6]
def baseStart_2216452 : Nat := 118140960795 + 2216452 * 2 ^ 59
def prefixEnd_2216452 : Nat := 4983230072969 + 3 ^ 40 * 2216452 * 2
def baseEnd_2216452 : Nat := 126456135957696372784081

theorem tailTrace_2216452 : CollatzResearch.WordTrace tailWord_2216452 prefixEnd_2216452 126456135957696372784081 := by
  unfold tailWord_2216452
  simp only [CollatzResearch.WordTrace]
  refine ⟨40420322883090209354805805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53893763844120279139741073 40420322883090209354805805)
  ·
    refine ⟨15157621081158828508052177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40420322883090209354805805 15157621081158828508052177)
    ·
      refine ⟨11368215810869121381039133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15157621081158828508052177 11368215810869121381039133)
      ·
        refine ⟨4263080929075920517889675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11368215810869121381039133 4263080929075920517889675)
        ·
          refine ⟨6394621393613880776834513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4263080929075920517889675 6394621393613880776834513)
          ·
            refine ⟨4795966045210410582625885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6394621393613880776834513 4795966045210410582625885)
            ·
              refine ⟨1798487266953903968484707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4795966045210410582625885 1798487266953903968484707)
              ·
                refine ⟨2697730900430855952727061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1798487266953903968484707 2697730900430855952727061)
                ·
                  refine ⟨126456135957696372784081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2697730900430855952727061 126456135957696372784081)
                  ·
                    rfl

theorem cell23_2216452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 1, 6].length) (baseStart_2216452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2216452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2216452 prefixEnd_2216452 := by exact prefixLift 2216452
  have htrace : WordTrace (prefixWord ++ tailWord_2216452) baseStart_2216452 baseEnd_2216452 := by
    simpa [prefixWord, tailWord_2216452, baseEnd_2216452] using wordTrace_append hprefix tailTrace_2216452
  have hstable : (prefixWord ++ tailWord_2216452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216452).length < 2 ^ (prefixWord ++ tailWord_2216452).sum := by decide
  have hdescent : baseEnd_2216452 < baseStart_2216452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216462 : List Nat := [4, 1, 1, 2, 3, 1, 2, 2, 3, 1, 3]
def baseStart_2216462 : Nat := 118140960795 + 2216462 * 2 ^ 59
def prefixEnd_2216462 : Nat := 4983230072969 + 3 ^ 40 * 2216462 * 2
def baseEnd_2216462 : Nat := 1138110358425812315931683

theorem tailTrace_2216462 : CollatzResearch.WordTrace tailWord_2216462 prefixEnd_2216462 1138110358425812315931683 := by
  unfold tailWord_2216462
  simp only [CollatzResearch.WordTrace]
  refine ⟨10105126312018023802184455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53894006997429460278317093 10105126312018023802184455)
  ·
    refine ⟨15157689468027035703276683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10105126312018023802184455 15157689468027035703276683)
    ·
      refine ⟨22736534202040553554915025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15157689468027035703276683 22736534202040553554915025)
      ·
        refine ⟨17052400651530415166186269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22736534202040553554915025 17052400651530415166186269)
        ·
          refine ⟨6394650244323905687319851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17052400651530415166186269 6394650244323905687319851)
          ·
            refine ⟨9591975366485858530979777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6394650244323905687319851 9591975366485858530979777)
            ·
              refine ⟨7193981524864393898234833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9591975366485858530979777 7193981524864393898234833)
              ·
                refine ⟨5395486143648295423676125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7193981524864393898234833 5395486143648295423676125)
                ·
                  refine ⟨2023307303868110783878547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5395486143648295423676125 2023307303868110783878547)
                  ·
                    refine ⟨3034960955802166175817821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2023307303868110783878547 3034960955802166175817821)
                    ·
                      refine ⟨1138110358425812315931683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3034960955802166175817821 1138110358425812315931683)
                      ·
                        rfl

theorem cell23_2216462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_2216462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2216462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2216462 prefixEnd_2216462 := by exact prefixLift 2216462
  have htrace : WordTrace (prefixWord ++ tailWord_2216462) baseStart_2216462 baseEnd_2216462 := by
    simpa [prefixWord, tailWord_2216462, baseEnd_2216462] using wordTrace_append hprefix tailTrace_2216462
  have hstable : (prefixWord ++ tailWord_2216462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216462).length < 2 ^ (prefixWord ++ tailWord_2216462).sum := by decide
  have hdescent : baseEnd_2216462 < baseStart_2216462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216485 : List Nat := [1, 3, 1, 2, 2, 1, 4, 3, 1, 1, 4]
def baseStart_2216485 : Nat := 118140960795 + 2216485 * 2 ^ 59
def prefixEnd_2216485 : Nat := 4983230072969 + 3 ^ 40 * 2216485 * 2
def baseEnd_2216485 : Nat := 1138122168480865725944077

theorem tailTrace_2216485 : CollatzResearch.WordTrace tailWord_2216485 prefixEnd_2216485 1138122168480865725944077 := by
  unfold tailWord_2216485
  simp only [CollatzResearch.WordTrace]
  refine ⟨80841849375060865345562909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53894566250040576897041939 80841849375060865345562909)
  ·
    refine ⟨30315693515647824504586091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80841849375060865345562909 30315693515647824504586091)
    ·
      refine ⟨45473540273471736756879137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30315693515647824504586091 45473540273471736756879137)
      ·
        refine ⟨34105155205103802567659353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45473540273471736756879137 34105155205103802567659353)
        ·
          refine ⟨25578866403827851925744515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34105155205103802567659353 25578866403827851925744515)
          ·
            refine ⟨38368299605741777888616773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25578866403827851925744515 38368299605741777888616773)
            ·
              refine ⟨7194056176076583354115645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38368299605741777888616773 7194056176076583354115645)
              ·
                refine ⟨2697771066028718757793367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7194056176076583354115645 2697771066028718757793367)
                ·
                  refine ⟨4046656599043078136690051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2697771066028718757793367 4046656599043078136690051)
                  ·
                    refine ⟨6069984898564617205035077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4046656599043078136690051 6069984898564617205035077)
                    ·
                      refine ⟨1138122168480865725944077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6069984898564617205035077 1138122168480865725944077)
                      ·
                        rfl

theorem cell23_2216485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 3, 1, 1, 4].length) (baseStart_2216485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2216485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2216485 prefixEnd_2216485 := by exact prefixLift 2216485
  have htrace : WordTrace (prefixWord ++ tailWord_2216485) baseStart_2216485 baseEnd_2216485 := by
    simpa [prefixWord, tailWord_2216485, baseEnd_2216485] using wordTrace_append hprefix tailTrace_2216485
  have hstable : (prefixWord ++ tailWord_2216485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216485).length < 2 ^ (prefixWord ++ tailWord_2216485).sum := by decide
  have hdescent : baseEnd_2216485 < baseStart_2216485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216498 : List Nat := [3, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6]
def baseStart_2216498 : Nat := 118140960795 + 2216498 * 2 ^ 59
def prefixEnd_2216498 : Nat := 4983230072969 + 3 ^ 40 * 2216498 * 2
def baseEnd_2216498 : Nat := 1138128843729374175081517

theorem tailTrace_2216498 : CollatzResearch.WordTrace tailWord_2216498 prefixEnd_2216498 1138128843729374175081517 := by
  unfold tailWord_2216498
  simp only [CollatzResearch.WordTrace]
  refine ⟨20210580881003442141446537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53894882349342512377190765 20210580881003442141446537)
  ·
    refine ⟨15157935660752581606084903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20210580881003442141446537 15157935660752581606084903)
    ·
      refine ⟨22736903491128872409127355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15157935660752581606084903 22736903491128872409127355)
      ·
        refine ⟨34105355236693308613691033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22736903491128872409127355 34105355236693308613691033)
        ·
          refine ⟨25579016427519981460268275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34105355236693308613691033 25579016427519981460268275)
          ·
            refine ⟨38368524641279972190402413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25579016427519981460268275 38368524641279972190402413)
            ·
              refine ⟨14388196740479989571400905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38368524641279972190402413 14388196740479989571400905)
              ·
                refine ⟨10791147555359992178550679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14388196740479989571400905 10791147555359992178550679)
                ·
                  refine ⟨16186721333039988267826019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10791147555359992178550679 16186721333039988267826019)
                  ·
                    refine ⟨24280081999559982401739029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16186721333039988267826019 24280081999559982401739029)
                    ·
                      refine ⟨1138128843729374175081517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24280081999559982401739029 1138128843729374175081517)
                      ·
                        rfl

theorem cell23_2216498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_2216498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2216498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2216498 prefixEnd_2216498 := by exact prefixLift 2216498
  have htrace : WordTrace (prefixWord ++ tailWord_2216498) baseStart_2216498 baseEnd_2216498 := by
    simpa [prefixWord, tailWord_2216498, baseEnd_2216498] using wordTrace_append hprefix tailTrace_2216498
  have hstable : (prefixWord ++ tailWord_2216498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216498).length < 2 ^ (prefixWord ++ tailWord_2216498).sum := by decide
  have hdescent : baseEnd_2216498 < baseStart_2216498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216505 : List Nat := [1, 2, 1, 5, 1, 1, 2, 2, 3, 2, 3]
def baseStart_2216505 : Nat := 118140960795 + 2216505 * 2 ^ 59
def prefixEnd_2216505 : Nat := 4983230072969 + 3 ^ 40 * 2216505 * 2
def baseEnd_2216505 : Nat := 1138132438093955647693985

theorem tailTrace_2216505 : CollatzResearch.WordTrace tailWord_2216505 prefixEnd_2216505 1138132438093955647693985 := by
  unfold tailWord_2216505
  simp only [CollatzResearch.WordTrace]
  refine ⟨80842578834988408761290969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53895052556658939174193979 80842578834988408761290969)
  ·
    refine ⟨60631934126241306570968227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80842578834988408761290969 60631934126241306570968227)
    ·
      refine ⟨90947901189361959856452341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60631934126241306570968227 90947901189361959856452341)
      ·
        refine ⟨8526365736502683736542407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 90947901189361959856452341 8526365736502683736542407)
        ·
          refine ⟨12789548604754025604813611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8526365736502683736542407 12789548604754025604813611)
          ·
            refine ⟨19184322907131038407220417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12789548604754025604813611 19184322907131038407220417)
            ·
              refine ⟨14388242180348278805415313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19184322907131038407220417 14388242180348278805415313)
              ·
                refine ⟨10791181635261209104061485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14388242180348278805415313 10791181635261209104061485)
                ·
                  refine ⟨4046693113222953414023057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10791181635261209104061485 4046693113222953414023057)
                  ·
                    refine ⟨3035019834917215060517293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4046693113222953414023057 3035019834917215060517293)
                    ·
                      refine ⟨1138132438093955647693985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3035019834917215060517293 1138132438093955647693985)
                      ·
                        rfl

theorem cell23_2216505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_2216505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2216505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2216505 prefixEnd_2216505 := by exact prefixLift 2216505
  have htrace : WordTrace (prefixWord ++ tailWord_2216505) baseStart_2216505 baseEnd_2216505 := by
    simpa [prefixWord, tailWord_2216505, baseEnd_2216505] using wordTrace_append hprefix tailTrace_2216505
  have hstable : (prefixWord ++ tailWord_2216505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216505).length < 2 ^ (prefixWord ++ tailWord_2216505).sum := by decide
  have hdescent : baseEnd_2216505 < baseStart_2216505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216508 : List Nat := [2, 2, 2, 2, 3, 1, 1, 10]
def baseStart_2216508 : Nat := 118140960795 + 2216508 * 2 ^ 59
def prefixEnd_2216508 : Nat := 4983230072969 + 3 ^ 40 * 2216508 * 2
def baseEnd_2216508 : Nat := 42153110316145153183573

theorem tailTrace_2216508 : CollatzResearch.WordTrace tailWord_2216508 prefixEnd_2216508 42153110316145153183573 := by
  unfold tailWord_2216508
  simp only [CollatzResearch.WordTrace]
  refine ⟨40421344126988770136825089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53895125502651693515766785 40421344126988770136825089)
  ·
    refine ⟨30316008095241577602618817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40421344126988770136825089 30316008095241577602618817)
    ·
      refine ⟨22737006071431183201964113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30316008095241577602618817 22737006071431183201964113)
      ·
        refine ⟨17052754553573387401473085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22737006071431183201964113 17052754553573387401473085)
        ·
          refine ⟨6394782957590020275552407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17052754553573387401473085 6394782957590020275552407)
          ·
            refine ⟨9592174436385030413328611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6394782957590020275552407 9592174436385030413328611)
            ·
              refine ⟨14388261654577545619992917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9592174436385030413328611 14388261654577545619992917)
              ·
                refine ⟨42153110316145153183573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 14388261654577545619992917 42153110316145153183573)
                ·
                  rfl

theorem cell23_2216508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 10].length) (baseStart_2216508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2216508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2216508 prefixEnd_2216508 := by exact prefixLift 2216508
  have htrace : WordTrace (prefixWord ++ tailWord_2216508) baseStart_2216508 baseEnd_2216508 := by
    simpa [prefixWord, tailWord_2216508, baseEnd_2216508] using wordTrace_append hprefix tailTrace_2216508
  have hstable : (prefixWord ++ tailWord_2216508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216508).length < 2 ^ (prefixWord ++ tailWord_2216508).sum := by decide
  have hdescent : baseEnd_2216508 < baseStart_2216508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216512 : List Nat := [2, 1, 1, 2, 2, 2, 6, 1, 2, 4]
def baseStart_2216512 : Nat := 118140960795 + 2216512 * 2 ^ 59
def prefixEnd_2216512 : Nat := 4983230072969 + 3 ^ 40 * 2216512 * 2
def baseEnd_2216512 : Nat := 379378677486179040102151

theorem tailTrace_2216512 : CollatzResearch.WordTrace tailWord_2216512 prefixEnd_2216512 379378677486179040102151 := by
  unfold tailWord_2216512
  simp only [CollatzResearch.WordTrace]
  refine ⟨40421417072981524478397895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53895222763975365971197193 40421417072981524478397895)
  ·
    refine ⟨60632125609472286717596843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40421417072981524478397895 60632125609472286717596843)
    ·
      refine ⟨90948188414208430076395265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60632125609472286717596843 90948188414208430076395265)
      ·
        refine ⟨68211141310656322557296449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90948188414208430076395265 68211141310656322557296449)
        ·
          refine ⟨51158355982992241917972337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68211141310656322557296449 51158355982992241917972337)
          ·
            refine ⟨38368766987244181438479253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51158355982992241917972337 38368766987244181438479253)
            ·
              refine ⟨1798535952527071004928715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38368766987244181438479253 1798535952527071004928715)
              ·
                refine ⟨2697803928790606507393073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1798535952527071004928715 2697803928790606507393073)
                ·
                  refine ⟨2023352946592954880544805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2697803928790606507393073 2023352946592954880544805)
                  ·
                    refine ⟨379378677486179040102151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2023352946592954880544805 379378677486179040102151)
                    ·
                      rfl

theorem cell23_2216512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 1, 2, 4].length) (baseStart_2216512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2216512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2216512 prefixEnd_2216512 := by exact prefixLift 2216512
  have htrace : WordTrace (prefixWord ++ tailWord_2216512) baseStart_2216512 baseEnd_2216512 := by
    simpa [prefixWord, tailWord_2216512, baseEnd_2216512] using wordTrace_append hprefix tailTrace_2216512
  have hstable : (prefixWord ++ tailWord_2216512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216512).length < 2 ^ (prefixWord ++ tailWord_2216512).sum := by decide
  have hdescent : baseEnd_2216512 < baseStart_2216512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216522 : List Nat := [3, 1, 2, 1, 1, 4, 3, 2, 1, 2, 3]
def baseStart_2216522 : Nat := 118140960795 + 2216522 * 2 ^ 59
def prefixEnd_2216522 : Nat := 4983230072969 + 3 ^ 40 * 2216522 * 2
def baseEnd_2216522 : Nat := 1138141167265082081181407

theorem tailTrace_2216522 : CollatzResearch.WordTrace tailWord_2216522 prefixEnd_2216522 1138141167265082081181407 := by
  unfold tailWord_2216522
  simp only [CollatzResearch.WordTrace]
  refine ⟨20210799718981705166164955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53895465917284547109773213 20210799718981705166164955)
  ·
    refine ⟨30316199578472557749247433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20210799718981705166164955 30316199578472557749247433)
    ·
      refine ⟨22737149683854418311935575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30316199578472557749247433 22737149683854418311935575)
      ·
        refine ⟨34105724525781627467903363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22737149683854418311935575 34105724525781627467903363)
        ·
          refine ⟨51158586788672441201855045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34105724525781627467903363 51158586788672441201855045)
          ·
            refine ⟨9592235022876082725347821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51158586788672441201855045 9592235022876082725347821)
            ·
              refine ⟨3597088133578531022005433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9592235022876082725347821 3597088133578531022005433)
              ·
                refine ⟨2697816100183898266504075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3597088133578531022005433 2697816100183898266504075)
                ·
                  refine ⟨4046724150275847399756113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2697816100183898266504075 4046724150275847399756113)
                  ·
                    refine ⟨3035043112706885549817085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4046724150275847399756113 3035043112706885549817085)
                    ·
                      refine ⟨1138141167265082081181407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3035043112706885549817085 1138141167265082081181407)
                      ·
                        rfl

theorem cell23_2216522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 2, 1, 2, 3].length) (baseStart_2216522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2216522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2216522 prefixEnd_2216522 := by exact prefixLift 2216522
  have htrace : WordTrace (prefixWord ++ tailWord_2216522) baseStart_2216522 baseEnd_2216522 := by
    simpa [prefixWord, tailWord_2216522, baseEnd_2216522] using wordTrace_append hprefix tailTrace_2216522
  have hstable : (prefixWord ++ tailWord_2216522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216522).length < 2 ^ (prefixWord ++ tailWord_2216522).sum := by decide
  have hdescent : baseEnd_2216522 < baseStart_2216522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216525 : List Nat := [1, 6, 1, 1, 2, 1, 2, 9]
def baseStart_2216525 : Nat := 118140960795 + 2216525 * 2 ^ 59
def prefixEnd_2216525 : Nat := 4983230072969 + 3 ^ 40 * 2216525 * 2
def baseEnd_2216525 : Nat := 42153433618779465534959

theorem tailTrace_2216525 : CollatzResearch.WordTrace tailWord_2216525 prefixEnd_2216525 42153433618779465534959 := by
  unfold tailWord_2216525
  simp only [CollatzResearch.WordTrace]
  refine ⟨80843308294915952177019029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53895538863277301451346019 80843308294915952177019029)
  ·
    refine ⟨3789530076324185258297767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 80843308294915952177019029 3789530076324185258297767)
    ·
      refine ⟨5684295114486277887446651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3789530076324185258297767 5684295114486277887446651)
      ·
        refine ⟨8526442671729416831169977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5684295114486277887446651 8526442671729416831169977)
        ·
          refine ⟨6394832003797062623377483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8526442671729416831169977 6394832003797062623377483)
          ·
            refine ⟨9592248005695593935066225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6394832003797062623377483 9592248005695593935066225)
            ·
              refine ⟨7194186004271695451299669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9592248005695593935066225 7194186004271695451299669)
              ·
                refine ⟨42153433618779465534959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7194186004271695451299669 42153433618779465534959)
                ·
                  rfl

theorem cell23_2216525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 9].length) (baseStart_2216525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2216525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2216525 prefixEnd_2216525 := by exact prefixLift 2216525
  have htrace : WordTrace (prefixWord ++ tailWord_2216525) baseStart_2216525 baseEnd_2216525 := by
    simpa [prefixWord, tailWord_2216525, baseEnd_2216525] using wordTrace_append hprefix tailTrace_2216525
  have hstable : (prefixWord ++ tailWord_2216525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216525).length < 2 ^ (prefixWord ++ tailWord_2216525).sum := by decide
  have hdescent : baseEnd_2216525 < baseStart_2216525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216535 : List Nat := [1, 1, 3, 2, 2, 2, 3, 2, 1, 3, 3]
def baseStart_2216535 : Nat := 118140960795 + 2216535 * 2 ^ 59
def prefixEnd_2216535 : Nat := 4983230072969 + 3 ^ 40 * 2216535 * 2
def baseEnd_2216535 : Nat := 1138147842513590530318847

theorem tailTrace_2216535 : CollatzResearch.WordTrace tailWord_2216535 prefixEnd_2216535 1138147842513590530318847 := by
  unfold tailWord_2216535
  simp only [CollatzResearch.WordTrace]
  refine ⟨80843673024879723884883059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53895782016586482589922039 80843673024879723884883059)
  ·
    refine ⟨121265509537319585827324589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80843673024879723884883059 121265509537319585827324589)
    ·
      refine ⟨45474566076494844685246721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 121265509537319585827324589 45474566076494844685246721)
      ·
        refine ⟨34105924557371133513935041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45474566076494844685246721 34105924557371133513935041)
        ·
          refine ⟨25579443418028350135451281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34105924557371133513935041 25579443418028350135451281)
          ·
            refine ⟨19184582563521262601588461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25579443418028350135451281 19184582563521262601588461)
            ·
              refine ⟨7194218461320473475595673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19184582563521262601588461 7194218461320473475595673)
              ·
                refine ⟨5395663845990355106696755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7194218461320473475595673 5395663845990355106696755)
                ·
                  refine ⟨8093495768985532660045133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5395663845990355106696755 8093495768985532660045133)
                  ·
                    refine ⟨3035060913369574747516925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8093495768985532660045133 3035060913369574747516925)
                    ·
                      refine ⟨1138147842513590530318847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3035060913369574747516925 1138147842513590530318847)
                      ·
                        rfl

theorem cell23_2216535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 3, 3].length) (baseStart_2216535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2216535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2216535 prefixEnd_2216535 := by exact prefixLift 2216535
  have htrace : WordTrace (prefixWord ++ tailWord_2216535) baseStart_2216535 baseEnd_2216535 := by
    simpa [prefixWord, tailWord_2216535, baseEnd_2216535] using wordTrace_append hprefix tailTrace_2216535
  have hstable : (prefixWord ++ tailWord_2216535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216535).length < 2 ^ (prefixWord ++ tailWord_2216535).sum := by decide
  have hdescent : baseEnd_2216535 < baseStart_2216535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216542 : List Nat := [4, 4, 1, 2, 12]
def baseStart_2216542 : Nat := 118140960795 + 2216542 * 2 ^ 59
def prefixEnd_2216542 : Nat := 4983230072969 + 3 ^ 40 * 2216542 * 2
def baseEnd_2216542 : Nat := 1561250256348658440235

theorem tailTrace_2216542 : CollatzResearch.WordTrace tailWord_2216542 prefixEnd_2216542 1561250256348658440235 := by
  unfold tailWord_2216542
  simp only [CollatzResearch.WordTrace]
  refine ⟨10105491041981795510048485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53895952223902909386925253 10105491041981795510048485)
  ·
    refine ⟨1894779570371586658134091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10105491041981795510048485 1894779570371586658134091)
    ·
      refine ⟨2842169355557379987201137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1894779570371586658134091 2842169355557379987201137)
      ·
        refine ⟨2131627016668034990400853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2842169355557379987201137 2131627016668034990400853)
        ·
          refine ⟨1561250256348658440235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 2131627016668034990400853 1561250256348658440235)
          ·
            rfl

theorem cell23_2216542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 12].length) (baseStart_2216542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2216542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2216542 prefixEnd_2216542 := by exact prefixLift 2216542
  have htrace : WordTrace (prefixWord ++ tailWord_2216542) baseStart_2216542 baseEnd_2216542 := by
    simpa [prefixWord, tailWord_2216542, baseEnd_2216542] using wordTrace_append hprefix tailTrace_2216542
  have hstable : (prefixWord ++ tailWord_2216542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216542).length < 2 ^ (prefixWord ++ tailWord_2216542).sum := by decide
  have hdescent : baseEnd_2216542 < baseStart_2216542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216546 : List Nat := [3, 3, 2, 3, 1, 1, 2, 2, 2, 4]
def baseStart_2216546 : Nat := 118140960795 + 2216546 * 2 ^ 59
def prefixEnd_2216546 : Nat := 4983230072969 + 3 ^ 40 * 2216546 * 2
def baseEnd_2216546 : Nat := 379384496933596662427099

theorem tailTrace_2216546 : CollatzResearch.WordTrace tailWord_2216546 prefixEnd_2216546 379384496933596662427099 := by
  unfold tailWord_2216546
  simp only [CollatzResearch.WordTrace]
  refine ⟨20211018556959968190883373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53896049485226581842355661 20211018556959968190883373)
  ·
    refine ⟨7579131958859988071581265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20211018556959968190883373 7579131958859988071581265)
    ·
      refine ⟨5684348969144991053685949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7579131958859988071581265 5684348969144991053685949)
      ·
        refine ⟨2131630863429371645132231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5684348969144991053685949 2131630863429371645132231)
        ·
          refine ⟨3197446295144057467698347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2131630863429371645132231 3197446295144057467698347)
          ·
            refine ⟨4796169442716086201547521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3197446295144057467698347 4796169442716086201547521)
            ·
              refine ⟨3597127082037064651160641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4796169442716086201547521 3597127082037064651160641)
              ·
                refine ⟨2697845311527798488370481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3597127082037064651160641 2697845311527798488370481)
                ·
                  refine ⟨2023383983645848866277861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2697845311527798488370481 2023383983645848866277861)
                  ·
                    refine ⟨379384496933596662427099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2023383983645848866277861 379384496933596662427099)
                    ·
                      rfl

theorem cell23_2216546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_2216546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2216546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2216546 prefixEnd_2216546 := by exact prefixLift 2216546
  have htrace : WordTrace (prefixWord ++ tailWord_2216546) baseStart_2216546 baseEnd_2216546 := by
    simpa [prefixWord, tailWord_2216546, baseEnd_2216546] using wordTrace_append hprefix tailTrace_2216546
  have hstable : (prefixWord ++ tailWord_2216546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216546).length < 2 ^ (prefixWord ++ tailWord_2216546).sum := by decide
  have hdescent : baseEnd_2216546 < baseStart_2216546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216568 : List Nat := [2, 1, 2, 1, 1, 1, 2, 5, 2, 6]
def baseStart_2216568 : Nat := 118140960795 + 2216568 * 2 ^ 59
def prefixEnd_2216568 : Nat := 4983230072969 + 3 ^ 40 * 2216568 * 2
def baseEnd_2216568 : Nat := 379388262458396300402065

theorem tailTrace_2216568 : CollatzResearch.WordTrace tailWord_2216568 prefixEnd_2216568 379388262458396300402065 := by
  unfold tailWord_2216568
  simp only [CollatzResearch.WordTrace]
  refine ⟨40422438316880085260417179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53896584422506780347222905 40422438316880085260417179)
  ·
    refine ⟨60633657475320127890625769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40422438316880085260417179 60633657475320127890625769)
    ·
      refine ⟨45475243106490095917969327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60633657475320127890625769 45475243106490095917969327)
      ·
        refine ⟨68212864659735143876953991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45475243106490095917969327 68212864659735143876953991)
        ·
          refine ⟨102319296989602715815430987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68212864659735143876953991 102319296989602715815430987)
          ·
            refine ⟨153478945484404073723146481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102319296989602715815430987 153478945484404073723146481)
            ·
              refine ⟨115109209113303055292359861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153478945484404073723146481 115109209113303055292359861)
              ·
                refine ⟨10791488354372161433658737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 115109209113303055292359861 10791488354372161433658737)
                ·
                  refine ⟨8093616265779121075244053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10791488354372161433658737 8093616265779121075244053)
                  ·
                    refine ⟨379388262458396300402065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8093616265779121075244053 379388262458396300402065)
                    ·
                      rfl

theorem cell23_2216568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 2, 6].length) (baseStart_2216568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2216568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2216568 prefixEnd_2216568 := by exact prefixLift 2216568
  have htrace : WordTrace (prefixWord ++ tailWord_2216568) baseStart_2216568 baseEnd_2216568 := by
    simpa [prefixWord, tailWord_2216568, baseEnd_2216568] using wordTrace_append hprefix tailTrace_2216568
  have hstable : (prefixWord ++ tailWord_2216568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216568).length < 2 ^ (prefixWord ++ tailWord_2216568).sum := by decide
  have hdescent : baseEnd_2216568 < baseStart_2216568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216596 : List Nat := [2, 4, 2, 2, 1, 2, 1, 3, 1, 3, 2]
def baseStart_2216596 : Nat := 118140960795 + 2216596 * 2 ^ 59
def prefixEnd_2216596 : Nat := 4983230072969 + 3 ^ 40 * 2216596 * 2
def baseEnd_2216596 : Nat := 1138179164833514791656067

theorem tailTrace_2216596 : CollatzResearch.WordTrace tailWord_2216596 prefixEnd_2216596 1138179164833514791656067 := by
  unfold tailWord_2216596
  simp only [CollatzResearch.WordTrace]
  refine ⟨40422948938829365651426821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53897265251772487535235761 40422948938829365651426821)
  ·
    refine ⟨7579302926030506059642529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40422948938829365651426821 7579302926030506059642529)
    ·
      refine ⟨5684477194522879544731897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7579302926030506059642529 5684477194522879544731897)
      ·
        refine ⟨4263357895892159658548923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5684477194522879544731897 4263357895892159658548923)
        ·
          refine ⟨6395036843838239487823385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4263357895892159658548923 6395036843838239487823385)
          ·
            refine ⟨4796277632878679615867539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6395036843838239487823385 4796277632878679615867539)
            ·
              refine ⟨7194416449318019423801309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4796277632878679615867539 7194416449318019423801309)
              ·
                refine ⟨2697906168494257283925491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7194416449318019423801309 2697906168494257283925491)
                ·
                  refine ⟨4046859252741385925888237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2697906168494257283925491 4046859252741385925888237)
                  ·
                    refine ⟨1517572219778019722208089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4046859252741385925888237 1517572219778019722208089)
                    ·
                      refine ⟨1138179164833514791656067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1517572219778019722208089 1138179164833514791656067)
                      ·
                        rfl

theorem cell23_2216596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_2216596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2216596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2216596 prefixEnd_2216596 := by exact prefixLift 2216596
  have htrace : WordTrace (prefixWord ++ tailWord_2216596) baseStart_2216596 baseEnd_2216596 := by
    simpa [prefixWord, tailWord_2216596, baseEnd_2216596] using wordTrace_append hprefix tailTrace_2216596
  have hstable : (prefixWord ++ tailWord_2216596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216596).length < 2 ^ (prefixWord ++ tailWord_2216596).sum := by decide
  have hdescent : baseEnd_2216596 < baseStart_2216596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216605 : List Nat := [1, 4, 2, 1, 1, 1, 3, 2, 2, 2, 4]
def baseStart_2216605 : Nat := 118140960795 + 2216605 * 2 ^ 59
def prefixEnd_2216605 : Nat := 4983230072969 + 3 ^ 40 * 2216605 * 2
def baseEnd_2216605 : Nat := 1138183786159405256443525

theorem tailTrace_2216605 : CollatzResearch.WordTrace tailWord_2216605 prefixEnd_2216605 1138183786159405256443525 := by
  unfold tailWord_2216605
  simp only [CollatzResearch.WordTrace]
  refine ⟨80846226134626125839931269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53897484089750750559954179 80846226134626125839931269)
  ·
    refine ⟨15158667400242398594987113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80846226134626125839931269 15158667400242398594987113)
    ·
      refine ⟨11369000550181798946240335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15158667400242398594987113 11369000550181798946240335)
      ·
        refine ⟨17053500825272698419360503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11369000550181798946240335 17053500825272698419360503)
        ·
          refine ⟨25580251237909047629040755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17053500825272698419360503 25580251237909047629040755)
          ·
            refine ⟨38370376856863571443561133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25580251237909047629040755 38370376856863571443561133)
            ·
              refine ⟨14388891321323839291335425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38370376856863571443561133 14388891321323839291335425)
              ·
                refine ⟨10791668490992879468501569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14388891321323839291335425 10791668490992879468501569)
                ·
                  refine ⟨8093751368244659601376177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10791668490992879468501569 8093751368244659601376177)
                  ·
                    refine ⟨6070313526183494701032133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8093751368244659601376177 6070313526183494701032133)
                    ·
                      refine ⟨1138183786159405256443525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6070313526183494701032133 1138183786159405256443525)
                      ·
                        rfl

theorem cell23_2216605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_2216605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2216605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2216605 prefixEnd_2216605 := by exact prefixLift 2216605
  have htrace : WordTrace (prefixWord ++ tailWord_2216605) baseStart_2216605 baseEnd_2216605 := by
    simpa [prefixWord, tailWord_2216605, baseEnd_2216605] using wordTrace_append hprefix tailTrace_2216605
  have hstable : (prefixWord ++ tailWord_2216605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216605).length < 2 ^ (prefixWord ++ tailWord_2216605).sum := by decide
  have hdescent : baseEnd_2216605 < baseStart_2216605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216646 : List Nat := [6, 1, 2, 1, 2, 1, 1, 1, 2, 1, 5]
def baseStart_2216646 : Nat := 118140960795 + 2216646 * 2 ^ 59
def prefixEnd_2216646 : Nat := 4983230072969 + 3 ^ 40 * 2216646 * 2
def baseEnd_2216646 : Nat := 1138204838866239596030837

theorem tailTrace_2216646 : CollatzResearch.WordTrace tailWord_2216646 prefixEnd_2216646 1138204838866239596030837 := by
  unfold tailWord_2216646
  simp only [CollatzResearch.WordTrace]
  refine ⟨2526491297733674682567931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 53898481018318393228115861 2526491297733674682567931)
  ·
    refine ⟨3789736946600512023851897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2526491297733674682567931 3789736946600512023851897)
    ·
      refine ⟨2842302709950384017888923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3789736946600512023851897 2842302709950384017888923)
      ·
        refine ⟨4263454064925576026833385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2842302709950384017888923 4263454064925576026833385)
        ·
          refine ⟨3197590548694182020125039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4263454064925576026833385 3197590548694182020125039)
          ·
            refine ⟨4796385823041273030187559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3197590548694182020125039 4796385823041273030187559)
            ·
              refine ⟨7194578734561909545281339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4796385823041273030187559 7194578734561909545281339)
              ·
                refine ⟨10791868101842864317922009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7194578734561909545281339 10791868101842864317922009)
                ·
                  refine ⟨8093901076382148238441507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10791868101842864317922009 8093901076382148238441507)
                  ·
                    refine ⟨12140851614573222357662261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8093901076382148238441507 12140851614573222357662261)
                    ·
                      refine ⟨1138204838866239596030837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12140851614573222357662261 1138204838866239596030837)
                      ·
                        rfl

theorem cell23_2216646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_2216646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2216646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2216646 prefixEnd_2216646 := by exact prefixLift 2216646
  have htrace : WordTrace (prefixWord ++ tailWord_2216646) baseStart_2216646 baseEnd_2216646 := by
    simpa [prefixWord, tailWord_2216646, baseEnd_2216646] using wordTrace_append hprefix tailTrace_2216646
  have hstable : (prefixWord ++ tailWord_2216646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216646).length < 2 ^ (prefixWord ++ tailWord_2216646).sum := by decide
  have hdescent : baseEnd_2216646 < baseStart_2216646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216682 : List Nat := [3, 1, 3, 1, 1, 1, 1, 3, 1, 6, 2]
def baseStart_2216682 : Nat := 118140960795 + 2216682 * 2 ^ 59
def prefixEnd_2216682 : Nat := 4983230072969 + 3 ^ 40 * 2216682 * 2
def baseEnd_2216682 : Nat := 1138223324169801455180671

theorem tailTrace_2216682 : CollatzResearch.WordTrace tailWord_2216682 prefixEnd_2216682 1138223324169801455180671 := by
  unfold tailWord_2216682
  simp only [CollatzResearch.WordTrace]
  refine ⟨20212258638836791997621075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53899356370231445326989533 20212258638836791997621075)
  ·
    refine ⟨30318387958255187996431613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20212258638836791997621075 30318387958255187996431613)
    ·
      refine ⟨11369395484345695498661855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30318387958255187996431613 11369395484345695498661855)
      ·
        refine ⟨17054093226518543247992783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11369395484345695498661855 17054093226518543247992783)
        ·
          refine ⟨25581139839777814871989175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17054093226518543247992783 25581139839777814871989175)
          ·
            refine ⟨38371709759666722307983763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25581139839777814871989175 38371709759666722307983763)
            ·
              refine ⟨57557564639500083461975645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38371709759666722307983763 57557564639500083461975645)
              ·
                refine ⟨21584086739812531298240867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57557564639500083461975645 21584086739812531298240867)
                ·
                  refine ⟨32376130109718796947361301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21584086739812531298240867 32376130109718796947361301)
                  ·
                    refine ⟨1517631098893068606907561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 32376130109718796947361301 1517631098893068606907561)
                    ·
                      refine ⟨1138223324169801455180671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1517631098893068606907561 1138223324169801455180671)
                      ·
                        rfl

theorem cell23_2216682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 1, 6, 2].length) (baseStart_2216682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2216682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2216682 prefixEnd_2216682 := by exact prefixLift 2216682
  have htrace : WordTrace (prefixWord ++ tailWord_2216682) baseStart_2216682 baseEnd_2216682 := by
    simpa [prefixWord, tailWord_2216682, baseEnd_2216682] using wordTrace_append hprefix tailTrace_2216682
  have hstable : (prefixWord ++ tailWord_2216682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216682).length < 2 ^ (prefixWord ++ tailWord_2216682).sum := by decide
  have hdescent : baseEnd_2216682 < baseStart_2216682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216725 : List Nat := [1, 3, 2, 1, 2, 2, 2, 1, 1, 2, 6]
def baseStart_2216725 : Nat := 118140960795 + 2216725 * 2 ^ 59
def prefixEnd_2216725 : Nat := 4983230072969 + 3 ^ 40 * 2216725 * 2
def baseEnd_2216725 : Nat := 1138245403837944786942973

theorem tailTrace_2216725 : CollatzResearch.WordTrace tailWord_2216725 prefixEnd_2216725 1138245403837944786942973 := by
  unfold tailWord_2216725
  simp only [CollatzResearch.WordTrace]
  refine ⟨80850602894191386334299629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53900401929460924222866419 80850602894191386334299629)
  ·
    refine ⟨30318976085321769875362361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80850602894191386334299629 30318976085321769875362361)
    ·
      refine ⟨22739232063991327406521771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30318976085321769875362361 22739232063991327406521771)
      ·
        refine ⟨34108848095986991109782657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22739232063991327406521771 34108848095986991109782657)
        ·
          refine ⟨25581636071990243332336993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34108848095986991109782657 25581636071990243332336993)
          ·
            refine ⟨19186227053992682499252745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25581636071990243332336993 19186227053992682499252745)
            ·
              refine ⟨14389670290494511874439559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19186227053992682499252745 14389670290494511874439559)
              ·
                refine ⟨21584505435741767811659339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14389670290494511874439559 21584505435741767811659339)
                ·
                  refine ⟨32376758153612651717489009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21584505435741767811659339 32376758153612651717489009)
                  ·
                    refine ⟨24282568615209488788116757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32376758153612651717489009 24282568615209488788116757)
                    ·
                      refine ⟨1138245403837944786942973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24282568615209488788116757 1138245403837944786942973)
                      ·
                        rfl

theorem cell23_2216725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_2216725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2216725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2216725 prefixEnd_2216725 := by exact prefixLift 2216725
  have htrace : WordTrace (prefixWord ++ tailWord_2216725) baseStart_2216725 baseEnd_2216725 := by
    simpa [prefixWord, tailWord_2216725, baseEnd_2216725] using wordTrace_append hprefix tailTrace_2216725
  have hstable : (prefixWord ++ tailWord_2216725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216725).length < 2 ^ (prefixWord ++ tailWord_2216725).sum := by decide
  have hdescent : baseEnd_2216725 < baseStart_2216725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216792 : List Nat := [2, 1, 2, 2, 1, 1, 1, 3, 5, 2, 3]
def baseStart_2216792 : Nat := 118140960795 + 2216792 * 2 ^ 59
def prefixEnd_2216792 : Nat := 4983230072969 + 3 ^ 40 * 2216792 * 2
def baseEnd_2216792 : Nat := 1138279807041796024805165

theorem tailTrace_2216792 : CollatzResearch.WordTrace tailWord_2216792 prefixEnd_2216792 1138279807041796024805165 := by
  unfold tailWord_2216792
  simp only [CollatzResearch.WordTrace]
  refine ⟨40426523292474328388494315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53902031056632437851325753 40426523292474328388494315)
  ·
    refine ⟨60639784938711492582741473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40426523292474328388494315 60639784938711492582741473)
    ·
      refine ⟨45479838704033619437056105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60639784938711492582741473 45479838704033619437056105)
      ·
        refine ⟨34109879028025214577792079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45479838704033619437056105 34109879028025214577792079)
        ·
          refine ⟨51164818542037821866688119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34109879028025214577792079 51164818542037821866688119)
          ·
            refine ⟨76747227813056732800032179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51164818542037821866688119 76747227813056732800032179)
            ·
              refine ⟨115120841719585099200048269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76747227813056732800032179 115120841719585099200048269)
              ·
                refine ⟨43170315644844412200018101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 115120841719585099200048269 43170315644844412200018101)
                ·
                  refine ⟨4047217091704163643751697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43170315644844412200018101 4047217091704163643751697)
                  ·
                    refine ⟨3035412818778122732813773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4047217091704163643751697 3035412818778122732813773)
                    ·
                      refine ⟨1138279807041796024805165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3035412818778122732813773 1138279807041796024805165)
                      ·
                        rfl

theorem cell23_2216792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 5, 2, 3].length) (baseStart_2216792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2216792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2216792 prefixEnd_2216792 := by exact prefixLift 2216792
  have htrace : WordTrace (prefixWord ++ tailWord_2216792) baseStart_2216792 baseEnd_2216792 := by
    simpa [prefixWord, tailWord_2216792, baseEnd_2216792] using wordTrace_append hprefix tailTrace_2216792
  have hstable : (prefixWord ++ tailWord_2216792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216792).length < 2 ^ (prefixWord ++ tailWord_2216792).sum := by decide
  have hdescent : baseEnd_2216792 < baseStart_2216792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216815 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 6]
def baseStart_2216815 : Nat := 118140960795 + 2216815 * 2 ^ 59
def prefixEnd_2216815 : Nat := 4983230072969 + 3 ^ 40 * 2216815 * 2
def baseEnd_2216815 : Nat := 1138291617096849434817559

theorem tailTrace_2216815 : CollatzResearch.WordTrace tailWord_2216815 prefixEnd_2216815 1138291617096849434817559 := by
  unfold tailWord_2216815
  simp only [CollatzResearch.WordTrace]
  refine ⟨80853885463865331705075899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53902590309243554470050599 80853885463865331705075899)
  ·
    refine ⟨121280828195797997557613849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80853885463865331705075899 121280828195797997557613849)
    ·
      refine ⟨90960621146848498168210387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121280828195797997557613849 90960621146848498168210387)
      ·
        refine ⟨136440931720272747252315581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90960621146848498168210387 136440931720272747252315581)
        ·
          refine ⟨51165349395102280219618343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136440931720272747252315581 51165349395102280219618343)
          ·
            refine ⟨76748024092653420329427515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51165349395102280219618343 76748024092653420329427515)
            ·
              refine ⟨115122036138980130494141273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76748024092653420329427515 115122036138980130494141273)
              ·
                refine ⟨86341527104235097870605955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115122036138980130494141273 86341527104235097870605955)
                ·
                  refine ⟨129512290656352646805908933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86341527104235097870605955 129512290656352646805908933)
                  ·
                    refine ⟨24283554498066121276107925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 129512290656352646805908933 24283554498066121276107925)
                    ·
                      refine ⟨1138291617096849434817559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24283554498066121276107925 1138291617096849434817559)
                      ·
                        rfl

theorem cell23_2216815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 6].length) (baseStart_2216815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2216815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2216815 prefixEnd_2216815 := by exact prefixLift 2216815
  have htrace : WordTrace (prefixWord ++ tailWord_2216815) baseStart_2216815 baseEnd_2216815 := by
    simpa [prefixWord, tailWord_2216815, baseEnd_2216815] using wordTrace_append hprefix tailTrace_2216815
  have hstable : (prefixWord ++ tailWord_2216815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216815).length < 2 ^ (prefixWord ++ tailWord_2216815).sum := by decide
  have hdescent : baseEnd_2216815 < baseStart_2216815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216834 : List Nat := [3, 4, 2, 2, 1, 1, 3, 2, 1, 1, 3]
def baseStart_2216834 : Nat := 118140960795 + 2216834 * 2 ^ 59
def prefixEnd_2216834 : Nat := 4983230072969 + 3 ^ 40 * 2216834 * 2
def baseEnd_2216834 : Nat := 1138301373229284860479973

theorem tailTrace_2216834 : CollatzResearch.WordTrace tailWord_2216834 prefixEnd_2216834 1138301373229284860479973 := by
  unfold tailWord_2216834
  simp only [CollatzResearch.WordTrace]
  refine ⟨20213644612699124487504389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53903052300530998633345037 20213644612699124487504389)
  ·
    refine ⟨3790058364881085841407073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20213644612699124487504389 3790058364881085841407073)
    ·
      refine ⟨2842543773660814381055305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3790058364881085841407073 2842543773660814381055305)
      ·
        refine ⟨2131907830245610785791479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2842543773660814381055305 2131907830245610785791479)
        ·
          refine ⟨3197861745368416178687219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2131907830245610785791479 3197861745368416178687219)
          ·
            refine ⟨4796792618052624268030829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3197861745368416178687219 4796792618052624268030829)
            ·
              refine ⟨1798797231769734100511561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4796792618052624268030829 1798797231769734100511561)
              ·
                refine ⟨1349097923827300575383671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1798797231769734100511561 1349097923827300575383671)
                ·
                  refine ⟨2023646885740950863075507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1349097923827300575383671 2023646885740950863075507)
                  ·
                    refine ⟨3035470328611426294613261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2023646885740950863075507 3035470328611426294613261)
                    ·
                      refine ⟨1138301373229284860479973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3035470328611426294613261 1138301373229284860479973)
                      ·
                        rfl

theorem cell23_2216834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_2216834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2216834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2216834 prefixEnd_2216834 := by exact prefixLift 2216834
  have htrace : WordTrace (prefixWord ++ tailWord_2216834) baseStart_2216834 baseEnd_2216834 := by
    simpa [prefixWord, tailWord_2216834, baseEnd_2216834] using wordTrace_append hprefix tailTrace_2216834
  have hstable : (prefixWord ++ tailWord_2216834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216834).length < 2 ^ (prefixWord ++ tailWord_2216834).sum := by decide
  have hdescent : baseEnd_2216834 < baseStart_2216834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216849 : List Nat := [1, 2, 2, 1, 1, 1, 3, 4, 3, 3, 2]
def baseStart_2216849 : Nat := 118140960795 + 2216849 * 2 ^ 59
def prefixEnd_2216849 : Nat := 4983230072969 + 3 ^ 40 * 2216849 * 2
def baseEnd_2216849 : Nat := 1138309075439102301792403

theorem tailTrace_2216849 : CollatzResearch.WordTrace tailWord_2216849 prefixEnd_2216849 1138309075439102301792403 := by
  unfold tailWord_2216849
  simp only [CollatzResearch.WordTrace]
  refine ⟨80855125545742155511813601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53903417030494770341209067 80855125545742155511813601)
  ·
    refine ⟨60641344159306616633860201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80855125545742155511813601 60641344159306616633860201)
    ·
      refine ⟨45481008119479962475395151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60641344159306616633860201 45481008119479962475395151)
      ·
        refine ⟨68221512179219943713092727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45481008119479962475395151 68221512179219943713092727)
        ·
          refine ⟨102332268268829915569639091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68221512179219943713092727 102332268268829915569639091)
          ·
            refine ⟨153498402403244873354458637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102332268268829915569639091 153498402403244873354458637)
            ·
              refine ⟨57561900901216827507921989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 153498402403244873354458637 57561900901216827507921989)
              ·
                refine ⟨10792856418978155157735373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57561900901216827507921989 10792856418978155157735373)
                ·
                  refine ⟨4047321157116808184150765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10792856418978155157735373 4047321157116808184150765)
                  ·
                    refine ⟨1517745433918803069056537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4047321157116808184150765 1517745433918803069056537)
                    ·
                      refine ⟨1138309075439102301792403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1517745433918803069056537 1138309075439102301792403)
                      ·
                        rfl

theorem cell23_2216849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 3, 2].length) (baseStart_2216849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2216849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2216849 prefixEnd_2216849 := by exact prefixLift 2216849
  have htrace : WordTrace (prefixWord ++ tailWord_2216849) baseStart_2216849 baseEnd_2216849 := by
    simpa [prefixWord, tailWord_2216849, baseEnd_2216849] using wordTrace_append hprefix tailTrace_2216849
  have hstable : (prefixWord ++ tailWord_2216849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216849).length < 2 ^ (prefixWord ++ tailWord_2216849).sum := by decide
  have hdescent : baseEnd_2216849 < baseStart_2216849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216850 : List Nat := [3, 2, 3, 2, 2, 2, 2, 1, 2, 4]
def baseStart_2216850 : Nat := 118140960795 + 2216850 * 2 ^ 59
def prefixEnd_2216850 : Nat := 4983230072969 + 3 ^ 40 * 2216850 * 2
def baseEnd_2216850 : Nat := 379436529639918932626633

theorem tailTrace_2216850 : CollatzResearch.WordTrace tailWord_2216850 prefixEnd_2216850 379436529639918932626633 := by
  unfold tailWord_2216850
  simp only [CollatzResearch.WordTrace]
  refine ⟨20213790504684633170650001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53903441345825688455066669 20213790504684633170650001)
  ·
    refine ⟨15160342878513474877987501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20213790504684633170650001 15160342878513474877987501)
    ·
      refine ⟨5685128579442553079245313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15160342878513474877987501 5685128579442553079245313)
      ·
        refine ⟨4263846434581914809433985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5685128579442553079245313 4263846434581914809433985)
        ·
          refine ⟨3197884825936436107075489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4263846434581914809433985 3197884825936436107075489)
          ·
            refine ⟨2398413619452327080306617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3197884825936436107075489 2398413619452327080306617)
            ·
              refine ⟨1798810214589245310229963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2398413619452327080306617 1798810214589245310229963)
              ·
                refine ⟨2698215321883867965344945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1798810214589245310229963 2698215321883867965344945)
                ·
                  refine ⟨2023661491412900974008709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2698215321883867965344945 2023661491412900974008709)
                  ·
                    refine ⟨379436529639918932626633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2023661491412900974008709 379436529639918932626633)
                    ·
                      rfl

theorem cell23_2216850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_2216850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2216850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2216850 prefixEnd_2216850 := by exact prefixLift 2216850
  have htrace : WordTrace (prefixWord ++ tailWord_2216850) baseStart_2216850 baseEnd_2216850 := by
    simpa [prefixWord, tailWord_2216850, baseEnd_2216850] using wordTrace_append hprefix tailTrace_2216850
  have hstable : (prefixWord ++ tailWord_2216850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216850).length < 2 ^ (prefixWord ++ tailWord_2216850).sum := by decide
  have hdescent : baseEnd_2216850 < baseStart_2216850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2216860 : List Nat := [2, 2, 3, 3, 3, 1, 1, 2, 1, 2, 3]
def baseStart_2216860 : Nat := 118140960795 + 2216860 * 2 ^ 59
def prefixEnd_2216860 : Nat := 4983230072969 + 3 ^ 40 * 2216860 * 2
def baseEnd_2216860 : Nat := 1138314723726301758754853

theorem tailTrace_2216860 : CollatzResearch.WordTrace tailWord_2216860 prefixEnd_2216860 1138314723726301758754853 := by
  unfold tailWord_2216860
  simp only [CollatzResearch.WordTrace]
  refine ⟨40427763374351152195232017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53903684499134869593642689 40427763374351152195232017)
  ·
    refine ⟨30320822530763364146424013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40427763374351152195232017 30320822530763364146424013)
    ·
      refine ⟨11370308449036261554909005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30320822530763364146424013 11370308449036261554909005)
      ·
        refine ⟨4263865668388598083090877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11370308449036261554909005 4263865668388598083090877)
        ·
          refine ⟨1598949625645724281159079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4263865668388598083090877 1598949625645724281159079)
          ·
            refine ⟨2398424438468586421738619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1598949625645724281159079 2398424438468586421738619)
            ·
              refine ⟨3597636657702879632607929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2398424438468586421738619 3597636657702879632607929)
              ·
                refine ⟨2698227493277159724455947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3597636657702879632607929 2698227493277159724455947)
                ·
                  refine ⟨4047341239915739586683921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2698227493277159724455947 4047341239915739586683921)
                  ·
                    refine ⟨3035505929936804690012941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4047341239915739586683921 3035505929936804690012941)
                    ·
                      refine ⟨1138314723726301758754853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3035505929936804690012941 1138314723726301758754853)
                      ·
                        rfl

theorem cell23_2216860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_2216860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2216860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2216860 prefixEnd_2216860 := by exact prefixLift 2216860
  have htrace : WordTrace (prefixWord ++ tailWord_2216860) baseStart_2216860 baseEnd_2216860 := by
    simpa [prefixWord, tailWord_2216860, baseEnd_2216860] using wordTrace_append hprefix tailTrace_2216860
  have hstable : (prefixWord ++ tailWord_2216860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2216860).length < 2 ^ (prefixWord ++ tailWord_2216860).sum := by decide
  have hdescent : baseEnd_2216860 < baseStart_2216860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2216860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217009 : List Nat := [1, 2, 2, 3, 1, 2, 2, 4, 6]
def baseStart_2217009 : Nat := 118140960795 + 2217009 * 2 ^ 59
def prefixEnd_2217009 : Nat := 4983230072969 + 3 ^ 40 * 2217009 * 2
def baseEnd_2217009 : Nat := 126487914704869075087963

theorem tailTrace_2217009 : CollatzResearch.WordTrace tailWord_2217009 prefixEnd_2217009 126487914704869075087963 := by
  unfold tailWord_2217009
  simp only [CollatzResearch.WordTrace]
  refine ⟨80860961225162502837638081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53907307483441668558425387 80860961225162502837638081)
  ·
    refine ⟨60645720918871877128228561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80860961225162502837638081 60645720918871877128228561)
    ·
      refine ⟨45484290689153907846171421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60645720918871877128228561 45484290689153907846171421)
      ·
        refine ⟨17056609008432715442314283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45484290689153907846171421 17056609008432715442314283)
        ·
          refine ⟨25584913512649073163471425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17056609008432715442314283 25584913512649073163471425)
          ·
            refine ⟨19188685134486804872603569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25584913512649073163471425 19188685134486804872603569)
            ·
              refine ⟨14391513850865103654452677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19188685134486804872603569 14391513850865103654452677)
              ·
                refine ⟨2698408847037206935209877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14391513850865103654452677 2698408847037206935209877)
                ·
                  refine ⟨126487914704869075087963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2698408847037206935209877 126487914704869075087963)
                  ·
                    rfl

theorem cell23_2217009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 4, 6].length) (baseStart_2217009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2217009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2217009 prefixEnd_2217009 := by exact prefixLift 2217009
  have htrace : WordTrace (prefixWord ++ tailWord_2217009) baseStart_2217009 baseEnd_2217009 := by
    simpa [prefixWord, tailWord_2217009, baseEnd_2217009] using wordTrace_append hprefix tailTrace_2217009
  have hstable : (prefixWord ++ tailWord_2217009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217009).length < 2 ^ (prefixWord ++ tailWord_2217009).sum := by decide
  have hdescent : baseEnd_2217009 < baseStart_2217009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217036 : List Nat := [2, 2, 1, 3, 1, 1, 1, 3, 5, 1, 3]
def baseStart_2217036 : Nat := 118140960795 + 2217036 * 2 ^ 59
def prefixEnd_2217036 : Nat := 4983230072969 + 3 ^ 40 * 2217036 * 2
def baseEnd_2217036 : Nat := 1138405096321493070154043

theorem tailTrace_2217036 : CollatzResearch.WordTrace tailWord_2217036 prefixEnd_2217036 1138405096321493070154043 := by
  unfold tailWord_2217036
  simp only [CollatzResearch.WordTrace]
  refine ⟨40430972998032343224435481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53907963997376457632580641 40430972998032343224435481)
  ·
    refine ⟨30323229748524257418326611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40430972998032343224435481 30323229748524257418326611)
    ·
      refine ⟨45484844622786386127489917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30323229748524257418326611 45484844622786386127489917)
      ·
        refine ⟨17056816733544894797808719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45484844622786386127489917 17056816733544894797808719)
        ·
          refine ⟨25585225100317342196713079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17056816733544894797808719 25585225100317342196713079)
          ·
            refine ⟨38377837650476013295069619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25585225100317342196713079 38377837650476013295069619)
            ·
              refine ⟨57566756475714019942604429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38377837650476013295069619 57566756475714019942604429)
              ·
                refine ⟨21587533678392757478476661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57566756475714019942604429 21587533678392757478476661)
                ·
                  refine ⟨2023831282349321013607187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21587533678392757478476661 2023831282349321013607187)
                  ·
                    refine ⟨3035746923523981520410781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2023831282349321013607187 3035746923523981520410781)
                    ·
                      refine ⟨1138405096321493070154043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3035746923523981520410781 1138405096321493070154043)
                      ·
                        rfl

theorem cell23_2217036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_2217036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2217036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2217036 prefixEnd_2217036 := by exact prefixLift 2217036
  have htrace : WordTrace (prefixWord ++ tailWord_2217036) baseStart_2217036 baseEnd_2217036 := by
    simpa [prefixWord, tailWord_2217036, baseEnd_2217036] using wordTrace_append hprefix tailTrace_2217036
  have hstable : (prefixWord ++ tailWord_2217036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217036).length < 2 ^ (prefixWord ++ tailWord_2217036).sum := by decide
  have hdescent : baseEnd_2217036 < baseStart_2217036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217063 : List Nat := [1, 1, 5, 1, 1, 3, 2, 2, 2, 3, 2]
def baseStart_2217063 : Nat := 118140960795 + 2217063 * 2 ^ 59
def prefixEnd_2217063 : Nat := 4983230072969 + 3 ^ 40 * 2217063 * 2
def baseEnd_2217063 : Nat := 1138418960299164464516419

theorem tailTrace_2217063 : CollatzResearch.WordTrace tailWord_2217063 prefixEnd_2217063 1138418960299164464516419 := by
  unfold tailWord_2217063
  simp only [CollatzResearch.WordTrace]
  refine ⟨80862930766966870060103843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53908620511311246706735895 80862930766966870060103843)
  ·
    refine ⟨121294396150450305090155765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80862930766966870060103843 121294396150450305090155765)
    ·
      refine ⟨11371349639104716102202103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 121294396150450305090155765 11371349639104716102202103)
      ·
        refine ⟨17057024458657074153303155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11371349639104716102202103 17057024458657074153303155)
        ·
          refine ⟨25585536687985611229954733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17057024458657074153303155 25585536687985611229954733)
          ·
            refine ⟨9594576257994604211233025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25585536687985611229954733 9594576257994604211233025)
            ·
              refine ⟨7195932193495953158424769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9594576257994604211233025 7195932193495953158424769)
              ·
                refine ⟨5396949145121964868818577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7195932193495953158424769 5396949145121964868818577)
                ·
                  refine ⟨4047711858841473651613933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5396949145121964868818577 4047711858841473651613933)
                  ·
                    refine ⟨1517891947065552619355225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4047711858841473651613933 1517891947065552619355225)
                    ·
                      refine ⟨1138418960299164464516419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1517891947065552619355225 1138418960299164464516419)
                      ·
                        rfl

theorem cell23_2217063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 2, 3, 2].length) (baseStart_2217063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2217063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2217063 prefixEnd_2217063 := by exact prefixLift 2217063
  have htrace : WordTrace (prefixWord ++ tailWord_2217063) baseStart_2217063 baseEnd_2217063 := by
    simpa [prefixWord, tailWord_2217063, baseEnd_2217063] using wordTrace_append hprefix tailTrace_2217063
  have hstable : (prefixWord ++ tailWord_2217063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217063).length < 2 ^ (prefixWord ++ tailWord_2217063).sum := by decide
  have hdescent : baseEnd_2217063 < baseStart_2217063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2217064 : List Nat := [2, 1, 4, 4, 1, 2, 2, 2, 1, 4]
def baseStart_2217064 : Nat := 118140960795 + 2217064 * 2 ^ 59
def prefixEnd_2217064 : Nat := 4983230072969 + 3 ^ 40 * 2217064 * 2
def baseEnd_2217064 : Nat := 379473157926606320201305

theorem tailTrace_2217064 : CollatzResearch.WordTrace tailWord_2217064 prefixEnd_2217064 379473157926606320201305 := by
  unfold tailWord_2217064
  simp only [CollatzResearch.WordTrace]
  refine ⟨40431483619981623615445123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53908644826642164820593497 40431483619981623615445123)
  ·
    refine ⟨60647225429972435423167685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40431483619981623615445123 60647225429972435423167685)
    ·
      refine ⟨11371354768119831641843941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60647225429972435423167685 11371354768119831641843941)
      ·
        refine ⟨2132129019022468432845739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11371354768119831641843941 2132129019022468432845739)
        ·
          refine ⟨3198193528533702649268609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2132129019022468432845739 3198193528533702649268609)
          ·
            refine ⟨2398645146400276986951457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3198193528533702649268609 2398645146400276986951457)
            ·
              refine ⟨1798983859800207740213593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2398645146400276986951457 1798983859800207740213593)
              ·
                refine ⟨1349237894850155805160195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1798983859800207740213593 1349237894850155805160195)
                ·
                  refine ⟨2023856842275233707740293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1349237894850155805160195 2023856842275233707740293)
                  ·
                    refine ⟨379473157926606320201305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2023856842275233707740293 379473157926606320201305)
                    ·
                      rfl

theorem cell23_2217064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_2217064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2217064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2217064 prefixEnd_2217064 := by exact prefixLift 2217064
  have htrace : WordTrace (prefixWord ++ tailWord_2217064) baseStart_2217064 baseEnd_2217064 := by
    simpa [prefixWord, tailWord_2217064, baseEnd_2217064] using wordTrace_append hprefix tailTrace_2217064
  have hstable : (prefixWord ++ tailWord_2217064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2217064).length < 2 ^ (prefixWord ++ tailWord_2217064).sum := by decide
  have hdescent : baseEnd_2217064 < baseStart_2217064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2217064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
