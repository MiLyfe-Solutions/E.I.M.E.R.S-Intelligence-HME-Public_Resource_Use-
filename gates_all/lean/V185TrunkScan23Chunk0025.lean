import V185TrunkScan23Chunk0024

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_147525 : List Nat := [1, 3, 1, 1, 1, 3, 1, 5, 3, 2, 2]
def baseStart_147525 : Nat := 118140960795 + 147525 * 2 ^ 59
def prefixEnd_147525 : Nat := 4983230072969 + 3 ^ 40 * 147525 * 2
def baseEnd_147525 : Nat := 75751233554640541459051

theorem tailTrace_147525 : CollatzResearch.WordTrace tailWord_147525 prefixEnd_147525 75751233554640541459051 := by
  unfold tailWord_147525
  simp only [CollatzResearch.WordTrace]
  refine ⟨5380678790549595109212029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3587119193699730072808019 5380678790549595109212029)
  ·
    refine ⟨2017754546456098165954511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5380678790549595109212029 2017754546456098165954511)
    ·
      refine ⟨3026631819684147248931767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2017754546456098165954511 3026631819684147248931767)
      ·
        refine ⟨4539947729526220873397651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3026631819684147248931767 4539947729526220873397651)
        ·
          refine ⟨6809921594289331310096477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4539947729526220873397651 6809921594289331310096477)
          ·
            refine ⟨2553720597858499241286179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6809921594289331310096477 2553720597858499241286179)
            ·
              refine ⟨3830580896787748861929269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2553720597858499241286179 3830580896787748861929269)
              ·
                refine ⟨359116959073851455805869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3830580896787748861929269 359116959073851455805869)
                ·
                  refine ⟨134668859652694295927201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 359116959073851455805869 134668859652694295927201)
                  ·
                    refine ⟨101001644739520721945401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 134668859652694295927201 101001644739520721945401)
                    ·
                      refine ⟨75751233554640541459051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 101001644739520721945401 75751233554640541459051)
                      ·
                        rfl

theorem cell23_147525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 3, 2, 2].length) (baseStart_147525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147525 prefixEnd_147525 := by exact prefixLift 147525
  have htrace : WordTrace (prefixWord ++ tailWord_147525) baseStart_147525 baseEnd_147525 := by
    simpa [prefixWord, tailWord_147525, baseEnd_147525] using wordTrace_append hprefix tailTrace_147525
  have hstable : (prefixWord ++ tailWord_147525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147525).length < 2 ^ (prefixWord ++ tailWord_147525).sum := by decide
  have hdescent : baseEnd_147525 < baseStart_147525 := by decide
  rcases family_descends (prefixWord ++ tailWord_147525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147542 : List Nat := [5, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4]
def baseStart_147542 : Nat := 118140960795 + 147542 * 2 ^ 59
def prefixEnd_147542 : Nat := 4983230072969 + 3 ^ 40 * 147542 * 2
def baseEnd_147542 : Nat := 75759962725766974946473

theorem tailTrace_147542 : CollatzResearch.WordTrace tailWord_147542 prefixEnd_147542 75759962725766974946473 := by
  unfold tailWord_147542
  simp only [CollatzResearch.WordTrace]
  refine ⟨336331176968000438286305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3587532554325338008387253 336331176968000438286305)
  ·
    refine ⟨252248382726000328714729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 336331176968000438286305 252248382726000328714729)
    ·
      refine ⟨189186287044500246536047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252248382726000328714729 189186287044500246536047)
      ·
        refine ⟨283779430566750369804071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189186287044500246536047 283779430566750369804071)
        ·
          refine ⟨425669145850125554706107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283779430566750369804071 425669145850125554706107)
          ·
            refine ⟨638503718775188332059161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 425669145850125554706107 638503718775188332059161)
            ·
              refine ⟨478877789081391249044371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 638503718775188332059161 478877789081391249044371)
              ·
                refine ⟨718316683622086873566557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 478877789081391249044371 718316683622086873566557)
                ·
                  refine ⟨269368756358282577587459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 718316683622086873566557 269368756358282577587459)
                  ·
                    refine ⟨404053134537423866381189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 269368756358282577587459 404053134537423866381189)
                    ·
                      refine ⟨75759962725766974946473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 404053134537423866381189 75759962725766974946473)
                      ·
                        rfl

theorem cell23_147542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_147542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147542 prefixEnd_147542 := by exact prefixLift 147542
  have htrace : WordTrace (prefixWord ++ tailWord_147542) baseStart_147542 baseEnd_147542 := by
    simpa [prefixWord, tailWord_147542, baseEnd_147542] using wordTrace_append hprefix tailTrace_147542
  have hstable : (prefixWord ++ tailWord_147542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147542).length < 2 ^ (prefixWord ++ tailWord_147542).sum := by decide
  have hdescent : baseEnd_147542 < baseStart_147542 := by decide
  rcases family_descends (prefixWord ++ tailWord_147542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147559 : List Nat := [1, 1, 5, 1, 1, 2, 4, 3, 1, 2, 2]
def baseStart_147559 : Nat := 118140960795 + 147559 * 2 ^ 59
def prefixEnd_147559 : Nat := 4983230072969 + 3 ^ 40 * 147559 * 2
def baseEnd_147559 : Nat := 75768691896893408433895

theorem tailTrace_147559 : CollatzResearch.WordTrace tailWord_147559 prefixEnd_147559 75768691896893408433895 := by
  unfold tailWord_147559
  simp only [CollatzResearch.WordTrace]
  refine ⟨5381918872426418915949731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3587945914950945943966487 5381918872426418915949731)
  ·
    refine ⟨8072878308639628373924597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5381918872426418915949731 8072878308639628373924597)
    ·
      refine ⟨756832341434965160055431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8072878308639628373924597 756832341434965160055431)
      ·
        refine ⟨1135248512152447740083147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 756832341434965160055431 1135248512152447740083147)
        ·
          refine ⟨1702872768228671610124721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1135248512152447740083147 1702872768228671610124721)
          ·
            refine ⟨1277154576171503707593541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1702872768228671610124721 1277154576171503707593541)
            ·
              refine ⟨239466483032156945173789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1277154576171503707593541 239466483032156945173789)
              ·
                refine ⟨89799931137058854440171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 239466483032156945173789 89799931137058854440171)
                ·
                  refine ⟨134699896705588281660257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89799931137058854440171 134699896705588281660257)
                  ·
                    refine ⟨101024922529191211245193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 134699896705588281660257 101024922529191211245193)
                    ·
                      refine ⟨75768691896893408433895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 101024922529191211245193 75768691896893408433895)
                      ·
                        rfl

theorem cell23_147559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 3, 1, 2, 2].length) (baseStart_147559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147559 prefixEnd_147559 := by exact prefixLift 147559
  have htrace : WordTrace (prefixWord ++ tailWord_147559) baseStart_147559 baseEnd_147559 := by
    simpa [prefixWord, tailWord_147559, baseEnd_147559] using wordTrace_append hprefix tailTrace_147559
  have hstable : (prefixWord ++ tailWord_147559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147559).length < 2 ^ (prefixWord ++ tailWord_147559).sum := by decide
  have hdescent : baseEnd_147559 < baseStart_147559 := by decide
  rcases family_descends (prefixWord ++ tailWord_147559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147562 : List Nat := [3, 1, 3, 2, 3, 1, 1, 3, 1, 2, 3]
def baseStart_147562 : Nat := 118140960795 + 147562 * 2 ^ 59
def prefixEnd_147562 : Nat := 4983230072969 + 3 ^ 40 * 147562 * 2
def baseEnd_147562 : Nat := 75770232338856896696381

theorem tailTrace_147562 : CollatzResearch.WordTrace tailWord_147562 prefixEnd_147562 75770232338856896696381 := by
  unfold tailWord_147562
  simp only [CollatzResearch.WordTrace]
  refine ⟨1345507072853887607077235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3588018860943700285539293 1345507072853887607077235)
  ·
    refine ⟨2018260609280831410615853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1345507072853887607077235 2018260609280831410615853)
    ·
      refine ⟨756847728480311778980945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2018260609280831410615853 756847728480311778980945)
      ·
        refine ⟨567635796360233834235709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 756847728480311778980945 567635796360233834235709)
        ·
          refine ⟨212863423635087687838391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 567635796360233834235709 212863423635087687838391)
          ·
            refine ⟨319295135452631531757587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212863423635087687838391 319295135452631531757587)
            ·
              refine ⟨478942703178947297636381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 319295135452631531757587 478942703178947297636381)
              ·
                refine ⟨179603513692105236613643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 478942703178947297636381 179603513692105236613643)
                ·
                  refine ⟨269405270538157854920465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 179603513692105236613643 269405270538157854920465)
                  ·
                    refine ⟨202053952903618391190349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 269405270538157854920465 202053952903618391190349)
                    ·
                      refine ⟨75770232338856896696381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 202053952903618391190349 75770232338856896696381)
                      ·
                        rfl

theorem cell23_147562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_147562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147562 prefixEnd_147562 := by exact prefixLift 147562
  have htrace : WordTrace (prefixWord ++ tailWord_147562) baseStart_147562 baseEnd_147562 := by
    simpa [prefixWord, tailWord_147562, baseEnd_147562] using wordTrace_append hprefix tailTrace_147562
  have hstable : (prefixWord ++ tailWord_147562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147562).length < 2 ^ (prefixWord ++ tailWord_147562).sum := by decide
  have hdescent : baseEnd_147562 < baseStart_147562 := by decide
  rcases family_descends (prefixWord ++ tailWord_147562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147575 : List Nat := [1, 1, 3, 1, 1, 6, 1, 1, 4, 1, 3]
def baseStart_147575 : Nat := 118140960795 + 147575 * 2 ^ 59
def prefixEnd_147575 : Nat := 4983230072969 + 3 ^ 40 * 147575 * 2
def baseEnd_147575 : Nat := 75776907587365345833821

theorem tailTrace_147575 : CollatzResearch.WordTrace tailWord_147575 prefixEnd_147575 75776907587365345833821 := by
  unfold tailWord_147575
  simp only [CollatzResearch.WordTrace]
  refine ⟨5382502440368453648532179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3588334960245635765688119 5382502440368453648532179)
  ·
    refine ⟨8073753660552680472798269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5382502440368453648532179 8073753660552680472798269)
    ·
      refine ⟨3027657622707255177299351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8073753660552680472798269 3027657622707255177299351)
      ·
        refine ⟨4541486434060882765949027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3027657622707255177299351 4541486434060882765949027)
        ·
          refine ⟨6812229651091324148923541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4541486434060882765949027 6812229651091324148923541)
          ·
            refine ⟨319323264894905819480791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6812229651091324148923541 319323264894905819480791)
            ·
              refine ⟨478984897342358729221187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 319323264894905819480791 478984897342358729221187)
              ·
                refine ⟨718477346013538093831781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 478984897342358729221187 718477346013538093831781)
                ·
                  refine ⟨134714502377538392593459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 718477346013538093831781 134714502377538392593459)
                  ·
                    refine ⟨202071753566307588890189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 134714502377538392593459 202071753566307588890189)
                    ·
                      refine ⟨75776907587365345833821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 202071753566307588890189 75776907587365345833821)
                      ·
                        rfl

theorem cell23_147575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 4, 1, 3].length) (baseStart_147575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147575 prefixEnd_147575 := by exact prefixLift 147575
  have htrace : WordTrace (prefixWord ++ tailWord_147575) baseStart_147575 baseEnd_147575 := by
    simpa [prefixWord, tailWord_147575, baseEnd_147575] using wordTrace_append hprefix tailTrace_147575
  have hstable : (prefixWord ++ tailWord_147575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147575).length < 2 ^ (prefixWord ++ tailWord_147575).sum := by decide
  have hdescent : baseEnd_147575 < baseStart_147575 := by decide
  rcases family_descends (prefixWord ++ tailWord_147575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147592 : List Nat := [2, 1, 3, 4, 1, 3, 1, 1, 1, 3, 3]
def baseStart_147592 : Nat := 118140960795 + 147592 * 2 ^ 59
def prefixEnd_147592 : Nat := 4983230072969 + 3 ^ 40 * 147592 * 2
def baseEnd_147592 : Nat := 75785636758491779321243

theorem tailTrace_147592 : CollatzResearch.WordTrace tailWord_147592 prefixEnd_147592 75785636758491779321243 := by
  unfold tailWord_147592
  simp only [CollatzResearch.WordTrace]
  refine ⟨2691561240653432775950515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3588748320871243701267353 2691561240653432775950515)
  ·
    refine ⟨4037341860980149163925773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2691561240653432775950515 4037341860980149163925773)
    ·
      refine ⟨1514003197867555936472165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4037341860980149163925773 1514003197867555936472165)
      ·
        refine ⟨283875599600166738088531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1514003197867555936472165 283875599600166738088531)
        ·
          refine ⟨425813399400250107132797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283875599600166738088531 425813399400250107132797)
          ·
            refine ⟨159680024775093790174799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 425813399400250107132797 159680024775093790174799)
            ·
              refine ⟨239520037162640685262199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159680024775093790174799 239520037162640685262199)
              ·
                refine ⟨359280055743961027893299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 239520037162640685262199 359280055743961027893299)
                ·
                  refine ⟨538920083615941541839949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 359280055743961027893299 538920083615941541839949)
                  ·
                    refine ⟨202095031355978078189981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 538920083615941541839949 202095031355978078189981)
                    ·
                      refine ⟨75785636758491779321243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 202095031355978078189981 75785636758491779321243)
                      ·
                        rfl

theorem cell23_147592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_147592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147592 prefixEnd_147592 := by exact prefixLift 147592
  have htrace : WordTrace (prefixWord ++ tailWord_147592) baseStart_147592 baseEnd_147592 := by
    simpa [prefixWord, tailWord_147592, baseEnd_147592] using wordTrace_append hprefix tailTrace_147592
  have hstable : (prefixWord ++ tailWord_147592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147592).length < 2 ^ (prefixWord ++ tailWord_147592).sum := by decide
  have hdescent : baseEnd_147592 < baseStart_147592 := by decide
  rcases family_descends (prefixWord ++ tailWord_147592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147601 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 5]
def baseStart_147601 : Nat := 118140960795 + 147601 * 2 ^ 59
def prefixEnd_147601 : Nat := 4983230072969 + 3 ^ 40 * 147601 * 2
def baseEnd_147601 : Nat := 75790258084382244108701

theorem tailTrace_147601 : CollatzResearch.WordTrace tailWord_147601 prefixEnd_147601 75790258084382244108701 := by
  unfold tailWord_147601
  simp only [CollatzResearch.WordTrace]
  refine ⟨5383450738274260088978657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3588967158849506725985771 5383450738274260088978657)
  ·
    refine ⟨4037588053705695066733993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5383450738274260088978657 4037588053705695066733993)
    ·
      refine ⟨3028191040279271300050495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4037588053705695066733993 3028191040279271300050495)
      ·
        refine ⟨4542286560418906950075743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3028191040279271300050495 4542286560418906950075743)
        ·
          refine ⟨6813429840628360425113615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4542286560418906950075743 6813429840628360425113615)
          ·
            refine ⟨10220144760942540637670423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6813429840628360425113615 10220144760942540637670423)
            ·
              refine ⟨15330217141413810956505635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10220144760942540637670423 15330217141413810956505635)
              ·
                refine ⟨22995325712120716434758453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15330217141413810956505635 22995325712120716434758453)
                ·
                  refine ⟨2155811785511317165758605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22995325712120716434758453 2155811785511317165758605)
                  ·
                    refine ⟨808429419566743937159477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2155811785511317165758605 808429419566743937159477)
                    ·
                      refine ⟨75790258084382244108701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 808429419566743937159477 75790258084382244108701)
                      ·
                        rfl

theorem cell23_147601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 5].length) (baseStart_147601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147601 prefixEnd_147601 := by exact prefixLift 147601
  have htrace : WordTrace (prefixWord ++ tailWord_147601) baseStart_147601 baseEnd_147601 := by
    simpa [prefixWord, tailWord_147601, baseEnd_147601] using wordTrace_append hprefix tailTrace_147601
  have hstable : (prefixWord ++ tailWord_147601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147601).length < 2 ^ (prefixWord ++ tailWord_147601).sum := by decide
  have hdescent : baseEnd_147601 < baseStart_147601 := by decide
  rcases family_descends (prefixWord ++ tailWord_147601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147631 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 9]
def baseStart_147631 : Nat := 118140960795 + 147631 * 2 ^ 59
def prefixEnd_147631 : Nat := 4983230072969 + 3 ^ 40 * 147631 * 2
def baseEnd_147631 : Nat := 75805662504017126733563

theorem tailTrace_147631 : CollatzResearch.WordTrace tailWord_147631 prefixEnd_147631 75805662504017126733563 := by
  unfold tailWord_147631
  simp only [CollatzResearch.WordTrace]
  refine ⟨5384544928165575212570747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3589696618777050141713831 5384544928165575212570747)
  ·
    refine ⟨8076817392248362818856121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5384544928165575212570747 8076817392248362818856121)
    ·
      refine ⟨6057613044186272114142091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8076817392248362818856121 6057613044186272114142091)
      ·
        refine ⟨9086419566279408171213137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6057613044186272114142091 9086419566279408171213137)
        ·
          refine ⟨6814814674709556128409853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9086419566279408171213137 6814814674709556128409853)
          ·
            refine ⟨2555555503016083548153695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6814814674709556128409853 2555555503016083548153695)
            ·
              refine ⟨3833333254524125322230543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2555555503016083548153695 3833333254524125322230543)
              ·
                refine ⟨5749999881786187983345815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3833333254524125322230543 5749999881786187983345815)
                ·
                  refine ⟨8624999822679281975018723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5749999881786187983345815 8624999822679281975018723)
                  ·
                    refine ⟨12937499734018922962528085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8624999822679281975018723 12937499734018922962528085)
                    ·
                      refine ⟨75805662504017126733563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 12937499734018922962528085 75805662504017126733563)
                      ·
                        rfl

theorem cell23_147631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 9].length) (baseStart_147631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147631 prefixEnd_147631 := by exact prefixLift 147631
  have htrace : WordTrace (prefixWord ++ tailWord_147631) baseStart_147631 baseEnd_147631 := by
    simpa [prefixWord, tailWord_147631, baseEnd_147631] using wordTrace_append hprefix tailTrace_147631
  have hstable : (prefixWord ++ tailWord_147631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147631).length < 2 ^ (prefixWord ++ tailWord_147631).sum := by decide
  have hdescent : baseEnd_147631 < baseStart_147631 := by decide
  rcases family_descends (prefixWord ++ tailWord_147631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147685 : List Nat := [1, 3, 1, 4, 2, 1, 2, 2, 2, 5]
def baseStart_147685 : Nat := 118140960795 + 147685 * 2 ^ 59
def prefixEnd_147685 : Nat := 4983230072969 + 3 ^ 40 * 147685 * 2
def baseEnd_147685 : Nat := 25277796819786638486105

theorem tailTrace_147685 : CollatzResearch.WordTrace tailWord_147685 prefixEnd_147685 25277796819786638486105 := by
  unfold tailWord_147685
  simp only [CollatzResearch.WordTrace]
  refine ⟨5386514469969942435036509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3591009646646628290024339 5386514469969942435036509)
  ·
    refine ⟨2019942926238728413138691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5386514469969942435036509 2019942926238728413138691)
    ·
      refine ⟨3029914389358092619708037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2019942926238728413138691 3029914389358092619708037)
      ·
        refine ⟨568108948004642366195257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3029914389358092619708037 568108948004642366195257)
        ·
          refine ⟨426081711003481774646443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 568108948004642366195257 426081711003481774646443)
          ·
            refine ⟨639122566505222661969665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 426081711003481774646443 639122566505222661969665)
            ·
              refine ⟨479341924878916996477249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 639122566505222661969665 479341924878916996477249)
              ·
                refine ⟨359506443659187747357937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 479341924878916996477249 359506443659187747357937)
                ·
                  refine ⟨269629832744390810518453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 359506443659187747357937 269629832744390810518453)
                  ·
                    refine ⟨25277796819786638486105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 269629832744390810518453 25277796819786638486105)
                    ·
                      rfl

theorem cell23_147685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 2, 5].length) (baseStart_147685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147685 prefixEnd_147685 := by exact prefixLift 147685
  have htrace : WordTrace (prefixWord ++ tailWord_147685) baseStart_147685 baseEnd_147685 := by
    simpa [prefixWord, tailWord_147685, baseEnd_147685] using wordTrace_append hprefix tailTrace_147685
  have hstable : (prefixWord ++ tailWord_147685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147685).length < 2 ^ (prefixWord ++ tailWord_147685).sum := by decide
  have hdescent : baseEnd_147685 < baseStart_147685 := by decide
  rcases family_descends (prefixWord ++ tailWord_147685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147715 : List Nat := [1, 1, 1, 3, 2, 3, 3, 2, 3, 4]
def baseStart_147715 : Nat := 118140960795 + 147715 * 2 ^ 59
def prefixEnd_147715 : Nat := 4983230072969 + 3 ^ 40 * 147715 * 2
def baseEnd_147715 : Nat := 25282931626331599361059

theorem tailTrace_147715 : CollatzResearch.WordTrace tailWord_147715 prefixEnd_147715 25282931626331599361059 := by
  unfold tailWord_147715
  simp only [CollatzResearch.WordTrace]
  refine ⟨5387608659861257558628599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3591739106574171705752399 5387608659861257558628599)
  ·
    refine ⟨8081412989791886337942899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5387608659861257558628599 8081412989791886337942899)
    ·
      refine ⟨12122119484687829506914349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8081412989791886337942899 12122119484687829506914349)
      ·
        refine ⟨4545794806757936065092881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12122119484687829506914349 4545794806757936065092881)
        ·
          refine ⟨3409346105068452048819661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4545794806757936065092881 3409346105068452048819661)
          ·
            refine ⟨1278504789400669518307373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3409346105068452048819661 1278504789400669518307373)
            ·
              refine ⟨479439296025251069365265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1278504789400669518307373 479439296025251069365265)
              ·
                refine ⟨359579472018938302023949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 479439296025251069365265 359579472018938302023949)
                ·
                  refine ⟨134842302007101863258981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 359579472018938302023949 134842302007101863258981)
                  ·
                    refine ⟨25282931626331599361059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 134842302007101863258981 25282931626331599361059)
                    ·
                      rfl

theorem cell23_147715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 3, 4].length) (baseStart_147715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147715 prefixEnd_147715 := by exact prefixLift 147715
  have htrace : WordTrace (prefixWord ++ tailWord_147715) baseStart_147715 baseEnd_147715 := by
    simpa [prefixWord, tailWord_147715, baseEnd_147715] using wordTrace_append hprefix tailTrace_147715
  have hstable : (prefixWord ++ tailWord_147715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147715).length < 2 ^ (prefixWord ++ tailWord_147715).sum := by decide
  have hdescent : baseEnd_147715 < baseStart_147715 := by decide
  rcases family_descends (prefixWord ++ tailWord_147715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147719 : List Nat := [1, 1, 4, 5, 1, 2, 1, 1, 2, 5]
def baseStart_147719 : Nat := 118140960795 + 147719 * 2 ^ 59
def prefixEnd_147719 : Nat := 4983230072969 + 3 ^ 40 * 147719 * 2
def baseEnd_147719 : Nat := 25283616267204260811053

theorem tailTrace_147719 : CollatzResearch.WordTrace tailWord_147719 prefixEnd_147719 25283616267204260811053 := by
  unfold tailWord_147719
  simp only [CollatzResearch.WordTrace]
  refine ⟨5387754551846766241774211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3591836367897844161182807 5387754551846766241774211)
  ·
    refine ⟨8081631827770149362661317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5387754551846766241774211 8081631827770149362661317)
    ·
      refine ⟨1515305967706903005498997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8081631827770149362661317 1515305967706903005498997)
      ·
        refine ⟨142059934472522156765531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1515305967706903005498997 142059934472522156765531)
        ·
          refine ⟨213089901708783235148297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142059934472522156765531 213089901708783235148297)
          ·
            refine ⟨159817426281587426361223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 213089901708783235148297 159817426281587426361223)
            ·
              refine ⟨239726139422381139541835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159817426281587426361223 239726139422381139541835)
              ·
                refine ⟨359589209133571709312753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 239726139422381139541835 359589209133571709312753)
                ·
                  refine ⟨269691906850178781984565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 359589209133571709312753 269691906850178781984565)
                  ·
                    refine ⟨25283616267204260811053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 269691906850178781984565 25283616267204260811053)
                    ·
                      rfl

theorem cell23_147719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 2, 5].length) (baseStart_147719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147719 prefixEnd_147719 := by exact prefixLift 147719
  have htrace : WordTrace (prefixWord ++ tailWord_147719) baseStart_147719 baseEnd_147719 := by
    simpa [prefixWord, tailWord_147719, baseEnd_147719] using wordTrace_append hprefix tailTrace_147719
  have hstable : (prefixWord ++ tailWord_147719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147719).length < 2 ^ (prefixWord ++ tailWord_147719).sum := by decide
  have hdescent : baseEnd_147719 < baseStart_147719 := by decide
  rcases family_descends (prefixWord ++ tailWord_147719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147745 : List Nat := [1, 2, 3, 2, 1, 1, 5, 2, 6]
def baseStart_147745 : Nat := 118140960795 + 147745 * 2 ^ 59
def prefixEnd_147745 : Nat := 4983230072969 + 3 ^ 40 * 147745 * 2
def baseEnd_147745 : Nat := 8429355477625520078671

theorem tailTrace_147745 : CollatzResearch.WordTrace tailWord_147745 prefixEnd_147745 8429355477625520078671 := by
  unfold tailWord_147745
  simp only [CollatzResearch.WordTrace]
  refine ⟨5388702849752572682220689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3592468566501715121480459 5388702849752572682220689)
  ·
    refine ⟨4041527137314429511665517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5388702849752572682220689 4041527137314429511665517)
    ·
      refine ⟨1515572676492911066874569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4041527137314429511665517 1515572676492911066874569)
      ·
        refine ⟨1136679507369683300155927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1515572676492911066874569 1136679507369683300155927)
        ·
          refine ⟨1705019261054524950233891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1136679507369683300155927 1705019261054524950233891)
          ·
            refine ⟨2557528891581787425350837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1705019261054524950233891 2557528891581787425350837)
            ·
              refine ⟨239768333585792571126641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2557528891581787425350837 239768333585792571126641)
              ·
                refine ⟨179826250189344428344981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 239768333585792571126641 179826250189344428344981)
                ·
                  refine ⟨8429355477625520078671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 179826250189344428344981 8429355477625520078671)
                  ·
                    rfl

theorem cell23_147745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 2, 6].length) (baseStart_147745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147745 prefixEnd_147745 := by exact prefixLift 147745
  have htrace : WordTrace (prefixWord ++ tailWord_147745) baseStart_147745 baseEnd_147745 := by
    simpa [prefixWord, tailWord_147745, baseEnd_147745] using wordTrace_append hprefix tailTrace_147745
  have hstable : (prefixWord ++ tailWord_147745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147745).length < 2 ^ (prefixWord ++ tailWord_147745).sum := by decide
  have hdescent : baseEnd_147745 < baseStart_147745 := by decide
  rcases family_descends (prefixWord ++ tailWord_147745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147768 : List Nat := [2, 1, 2, 1, 3, 1, 2, 1, 2, 1, 7]
def baseStart_147768 : Nat := 118140960795 + 147768 * 2 ^ 59
def prefixEnd_147768 : Nat := 4983230072969 + 3 ^ 40 * 147768 * 2
def baseEnd_147768 : Nat := 75876009353683090720433

theorem tailTrace_147768 : CollatzResearch.WordTrace tailWord_147768 prefixEnd_147768 75876009353683090720433 := by
  unfold tailWord_147768
  simp only [CollatzResearch.WordTrace]
  refine ⟨2694770864334623805153979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3593027819112831740205305 2694770864334623805153979)
  ·
    refine ⟨4042156296501935707730969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2694770864334623805153979 4042156296501935707730969)
    ·
      refine ⟨3031617222376451780798227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4042156296501935707730969 3031617222376451780798227)
      ·
        refine ⟨4547425833564677671197341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3031617222376451780798227 4547425833564677671197341)
        ·
          refine ⟨1705284687586754126699003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4547425833564677671197341 1705284687586754126699003)
          ·
            refine ⟨2557927031380131190048505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1705284687586754126699003 2557927031380131190048505)
            ·
              refine ⟨1918445273535098392536379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2557927031380131190048505 1918445273535098392536379)
              ·
                refine ⟨2877667910302647588804569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1918445273535098392536379 2877667910302647588804569)
                ·
                  refine ⟨2158250932726985691603427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2877667910302647588804569 2158250932726985691603427)
                  ·
                    refine ⟨3237376399090478537405141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2158250932726985691603427 3237376399090478537405141)
                    ·
                      refine ⟨75876009353683090720433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 3237376399090478537405141 75876009353683090720433)
                      ·
                        rfl

theorem cell23_147768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 2, 1, 7].length) (baseStart_147768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147768 prefixEnd_147768 := by exact prefixLift 147768
  have htrace : WordTrace (prefixWord ++ tailWord_147768) baseStart_147768 baseEnd_147768 := by
    simpa [prefixWord, tailWord_147768, baseEnd_147768] using wordTrace_append hprefix tailTrace_147768
  have hstable : (prefixWord ++ tailWord_147768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147768).length < 2 ^ (prefixWord ++ tailWord_147768).sum := by decide
  have hdescent : baseEnd_147768 < baseStart_147768 := by decide
  rcases family_descends (prefixWord ++ tailWord_147768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147772 : List Nat := [2, 2, 2, 2, 1, 2, 1, 4, 3, 1, 3]
def baseStart_147772 : Nat := 118140960795 + 147772 * 2 ^ 59
def prefixEnd_147772 : Nat := 4983230072969 + 3 ^ 40 * 147772 * 2
def baseEnd_147772 : Nat := 75878063276301075070415

theorem tailTrace_147772 : CollatzResearch.WordTrace tailWord_147772 prefixEnd_147772 75878063276301075070415 := by
  unfold tailWord_147772
  simp only [CollatzResearch.WordTrace]
  refine ⟨2694843810327378146726785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3593125080436504195635713 2694843810327378146726785)
  ·
    refine ⟨2021132857745533610045089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2694843810327378146726785 2021132857745533610045089)
    ·
      refine ⟨1515849643309150207533817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2021132857745533610045089 1515849643309150207533817)
      ·
        refine ⟨1136887232481862655650363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1515849643309150207533817 1136887232481862655650363)
        ·
          refine ⟨1705330848722793983475545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1136887232481862655650363 1705330848722793983475545)
          ·
            refine ⟨1278998136542095487606659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1705330848722793983475545 1278998136542095487606659)
            ·
              refine ⟨1918497204813143231409989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1278998136542095487606659 1918497204813143231409989)
              ·
                refine ⟨359718225902464355889373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1918497204813143231409989 359718225902464355889373)
                ·
                  refine ⟨134894334713424133458515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 359718225902464355889373 134894334713424133458515)
                  ·
                    refine ⟨202341502070136200187773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 134894334713424133458515 202341502070136200187773)
                    ·
                      refine ⟨75878063276301075070415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 202341502070136200187773 75878063276301075070415)
                      ·
                        rfl

theorem cell23_147772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_147772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147772 prefixEnd_147772 := by exact prefixLift 147772
  have htrace : WordTrace (prefixWord ++ tailWord_147772) baseStart_147772 baseEnd_147772 := by
    simpa [prefixWord, tailWord_147772, baseEnd_147772] using wordTrace_append hprefix tailTrace_147772
  have hstable : (prefixWord ++ tailWord_147772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147772).length < 2 ^ (prefixWord ++ tailWord_147772).sum := by decide
  have hdescent : baseEnd_147772 < baseStart_147772 := by decide
  rcases family_descends (prefixWord ++ tailWord_147772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147825 : List Nat := [1, 2, 2, 2, 1, 2, 1, 5, 1, 2, 4]
def baseStart_147825 : Nat := 118140960795 + 147825 * 2 ^ 59
def prefixEnd_147825 : Nat := 4983230072969 + 3 ^ 40 * 147825 * 2
def baseEnd_147825 : Nat := 75905277750989367707671

theorem tailTrace_147825 : CollatzResearch.WordTrace tailWord_147825 prefixEnd_147825 75905277750989367707671 := by
  unfold tailWord_147825
  simp only [CollatzResearch.WordTrace]
  refine ⟨5391620689462746345132929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3594413792975164230088619 5391620689462746345132929)
  ·
    refine ⟨4043715517097059758849697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5391620689462746345132929 4043715517097059758849697)
    ·
      refine ⟨3032786637822794819137273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4043715517097059758849697 3032786637822794819137273)
      ·
        refine ⟨2274589978367096114352955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3032786637822794819137273 2274589978367096114352955)
        ·
          refine ⟨3411884967550644171529433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2274589978367096114352955 3411884967550644171529433)
          ·
            refine ⟨2558913725662983128647075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3411884967550644171529433 2558913725662983128647075)
            ·
              refine ⟨3838370588494474692970613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2558913725662983128647075 3838370588494474692970613)
              ·
                refine ⟨359847242671357002465995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3838370588494474692970613 359847242671357002465995)
                ·
                  refine ⟨539770864007035503698993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 359847242671357002465995 539770864007035503698993)
                  ·
                    refine ⟨404828148005276627774245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 539770864007035503698993 404828148005276627774245)
                    ·
                      refine ⟨75905277750989367707671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 404828148005276627774245 75905277750989367707671)
                      ·
                        rfl

theorem cell23_147825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_147825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147825 prefixEnd_147825 := by exact prefixLift 147825
  have htrace : WordTrace (prefixWord ++ tailWord_147825) baseStart_147825 baseEnd_147825 := by
    simpa [prefixWord, tailWord_147825, baseEnd_147825] using wordTrace_append hprefix tailTrace_147825
  have hstable : (prefixWord ++ tailWord_147825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147825).length < 2 ^ (prefixWord ++ tailWord_147825).sum := by decide
  have hdescent : baseEnd_147825 < baseStart_147825 := by decide
  rcases family_descends (prefixWord ++ tailWord_147825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147829 : List Nat := [1, 3, 4, 1, 2, 1, 3, 2, 1, 1, 4]
def baseStart_147829 : Nat := 118140960795 + 147829 * 2 ^ 59
def prefixEnd_147829 : Nat := 4983230072969 + 3 ^ 40 * 147829 * 2
def baseEnd_147829 : Nat := 75907331673607352057653

theorem tailTrace_147829 : CollatzResearch.WordTrace tailWord_147829 prefixEnd_147829 75907331673607352057653 := by
  unfold tailWord_147829
  simp only [CollatzResearch.WordTrace]
  refine ⟨5391766581448255028278541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3594511054298836685519027 5391766581448255028278541)
  ·
    refine ⟨2021912468043095635604453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5391766581448255028278541 2021912468043095635604453)
    ·
      refine ⟨379108587758080431675835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2021912468043095635604453 379108587758080431675835)
      ·
        refine ⟨568662881637120647513753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379108587758080431675835 568662881637120647513753)
        ·
          refine ⟨426497161227840485635315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 568662881637120647513753 426497161227840485635315)
          ·
            refine ⟨639745741841760728452973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 426497161227840485635315 639745741841760728452973)
            ·
              refine ⟨239904653190660273169865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 639745741841760728452973 239904653190660273169865)
              ·
                refine ⟨179928489892995204877399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 239904653190660273169865 179928489892995204877399)
                ·
                  refine ⟨269892734839492807316099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 179928489892995204877399 269892734839492807316099)
                  ·
                    refine ⟨404839102259239210974149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 269892734839492807316099 404839102259239210974149)
                    ·
                      refine ⟨75907331673607352057653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 404839102259239210974149 75907331673607352057653)
                      ·
                        rfl

theorem cell23_147829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_147829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147829 prefixEnd_147829 := by exact prefixLift 147829
  have htrace : WordTrace (prefixWord ++ tailWord_147829) baseStart_147829 baseEnd_147829 := by
    simpa [prefixWord, tailWord_147829, baseEnd_147829] using wordTrace_append hprefix tailTrace_147829
  have hstable : (prefixWord ++ tailWord_147829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147829).length < 2 ^ (prefixWord ++ tailWord_147829).sum := by decide
  have hdescent : baseEnd_147829 < baseStart_147829 := by decide
  rcases family_descends (prefixWord ++ tailWord_147829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147863 : List Nat := [1, 1, 3, 3, 1, 1, 6, 2, 1, 2, 2]
def baseStart_147863 : Nat := 118140960795 + 147863 * 2 ^ 59
def prefixEnd_147863 : Nat := 4983230072969 + 3 ^ 40 * 147863 * 2
def baseEnd_147863 : Nat := 75924790015860219032497

theorem tailTrace_147863 : CollatzResearch.WordTrace tailWord_147863 prefixEnd_147863 75924790015860219032497 := by
  unfold tailWord_147863
  simp only [CollatzResearch.WordTrace]
  refine ⟨5393006663325078835016243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3595337775550052556677495 5393006663325078835016243)
  ·
    refine ⟨8089509994987618252524365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5393006663325078835016243 8089509994987618252524365)
    ·
      refine ⟨3033566248120356844696637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8089509994987618252524365 3033566248120356844696637)
      ·
        refine ⟨1137587343045133816761239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3033566248120356844696637 1137587343045133816761239)
        ·
          refine ⟨1706381014567700725141859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1137587343045133816761239 1706381014567700725141859)
          ·
            refine ⟨2559571521851551087712789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1706381014567700725141859 2559571521851551087712789)
            ·
              refine ⟨119979915086791457236537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2559571521851551087712789 119979915086791457236537)
              ·
                refine ⟨89984936315093592927403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119979915086791457236537 89984936315093592927403)
                ·
                  refine ⟨134977404472640389391105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89984936315093592927403 134977404472640389391105)
                  ·
                    refine ⟨101233053354480292043329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 134977404472640389391105 101233053354480292043329)
                    ·
                      refine ⟨75924790015860219032497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 101233053354480292043329 75924790015860219032497)
                      ·
                        rfl

theorem cell23_147863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 2, 1, 2, 2].length) (baseStart_147863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147863 prefixEnd_147863 := by exact prefixLift 147863
  have htrace : WordTrace (prefixWord ++ tailWord_147863) baseStart_147863 baseEnd_147863 := by
    simpa [prefixWord, tailWord_147863, baseEnd_147863] using wordTrace_append hprefix tailTrace_147863
  have hstable : (prefixWord ++ tailWord_147863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147863).length < 2 ^ (prefixWord ++ tailWord_147863).sum := by decide
  have hdescent : baseEnd_147863 < baseStart_147863 := by decide
  rcases family_descends (prefixWord ++ tailWord_147863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147869 : List Nat := [1, 4, 2, 1, 5, 1, 1, 8]
def baseStart_147869 : Nat := 118140960795 + 147869 * 2 ^ 59
def prefixEnd_147869 : Nat := 4983230072969 + 3 ^ 40 * 147869 * 2
def baseEnd_147869 : Nat := 2812143366658785020647

theorem tailTrace_147869 : CollatzResearch.WordTrace tailWord_147869 prefixEnd_147869 2812143366658785020647 := by
  unfold tailWord_147869
  simp only [CollatzResearch.WordTrace]
  refine ⟨5393225501303341859734661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3595483667535561239823107 5393225501303341859734661)
  ·
    refine ⟨1011229781494376598700249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5393225501303341859734661 1011229781494376598700249)
    ·
      refine ⟨758422336120782449025187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1011229781494376598700249 758422336120782449025187)
      ·
        refine ⟨1137633504181173673537781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 758422336120782449025187 1137633504181173673537781)
        ·
          refine ⟨106653141016985031894167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1137633504181173673537781 106653141016985031894167)
          ·
            refine ⟨159979711525477547841251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106653141016985031894167 159979711525477547841251)
            ·
              refine ⟨239969567288216321761877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159979711525477547841251 239969567288216321761877)
              ·
                refine ⟨2812143366658785020647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 239969567288216321761877 2812143366658785020647)
                ·
                  rfl

theorem cell23_147869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 8].length) (baseStart_147869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147869 prefixEnd_147869 := by exact prefixLift 147869
  have htrace : WordTrace (prefixWord ++ tailWord_147869) baseStart_147869 baseEnd_147869 := by
    simpa [prefixWord, tailWord_147869, baseEnd_147869] using wordTrace_append hprefix tailTrace_147869
  have hstable : (prefixWord ++ tailWord_147869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147869).length < 2 ^ (prefixWord ++ tailWord_147869).sum := by decide
  have hdescent : baseEnd_147869 < baseStart_147869 := by decide
  rcases family_descends (prefixWord ++ tailWord_147869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147879 : List Nat := [1, 1, 6, 1, 1, 3, 2, 1, 1, 3, 3]
def baseStart_147879 : Nat := 118140960795 + 147879 * 2 ^ 59
def prefixEnd_147879 : Nat := 4983230072969 + 3 ^ 40 * 147879 * 2
def baseEnd_147879 : Nat := 75933005706332156432423

theorem tailTrace_147879 : CollatzResearch.WordTrace tailWord_147879 prefixEnd_147879 75933005706332156432423 := by
  unfold tailWord_147879
  simp only [CollatzResearch.WordTrace]
  refine ⟨5393590231267113567598691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3595726820844742378399127 5393590231267113567598691)
  ·
    refine ⟨8090385346900670351398037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5393590231267113567598691 8090385346900670351398037)
    ·
      refine ⟨379236813135968922721783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8090385346900670351398037 379236813135968922721783)
      ·
        refine ⟨568855219703953384082675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379236813135968922721783 568855219703953384082675)
        ·
          refine ⟨853282829555930076124013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 568855219703953384082675 853282829555930076124013)
          ·
            refine ⟨319981061083473778546505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 853282829555930076124013 319981061083473778546505)
            ·
              refine ⟨239985795812605333909879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 319981061083473778546505 239985795812605333909879)
              ·
                refine ⟨359978693718908000864819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 239985795812605333909879 359978693718908000864819)
                ·
                  refine ⟨539968040578362001297229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 359978693718908000864819 539968040578362001297229)
                  ·
                    refine ⟨202488015216885750486461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 539968040578362001297229 202488015216885750486461)
                    ·
                      refine ⟨75933005706332156432423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 202488015216885750486461 75933005706332156432423)
                      ·
                        rfl

theorem cell23_147879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_147879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147879 prefixEnd_147879 := by exact prefixLift 147879
  have htrace : WordTrace (prefixWord ++ tailWord_147879) baseStart_147879 baseEnd_147879 := by
    simpa [prefixWord, tailWord_147879, baseEnd_147879] using wordTrace_append hprefix tailTrace_147879
  have hstable : (prefixWord ++ tailWord_147879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147879).length < 2 ^ (prefixWord ++ tailWord_147879).sum := by decide
  have hdescent : baseEnd_147879 < baseStart_147879 := by decide
  rcases family_descends (prefixWord ++ tailWord_147879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147889 : List Nat := [1, 2, 2, 4, 1, 2, 2, 1, 3, 3, 2]
def baseStart_147889 : Nat := 118140960795 + 147889 * 2 ^ 59
def prefixEnd_147889 : Nat := 4983230072969 + 3 ^ 40 * 147889 * 2
def baseEnd_147889 : Nat := 75938140512877117307377

theorem tailTrace_147889 : CollatzResearch.WordTrace tailWord_147889 prefixEnd_147889 75938140512877117307377 := by
  unfold tailWord_147889
  simp only [CollatzResearch.WordTrace]
  refine ⟨5393954961230885275462721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3595969974153923516975147 5393954961230885275462721)
  ·
    refine ⟨4045466220923163956597041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5393954961230885275462721 4045466220923163956597041)
    ·
      refine ⟨3034099665692372967447781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4045466220923163956597041 3034099665692372967447781)
      ·
        refine ⟨568893687317319931396459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3034099665692372967447781 568893687317319931396459)
        ·
          refine ⟨853340530975979897094689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 568893687317319931396459 853340530975979897094689)
          ·
            refine ⟨640005398231984922821017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 853340530975979897094689 640005398231984922821017)
            ·
              refine ⟨480004048673988692115763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 640005398231984922821017 480004048673988692115763)
              ·
                refine ⟨720006073010983038173645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 480004048673988692115763 720006073010983038173645)
                ·
                  refine ⟨270002277379118639315117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 720006073010983038173645 270002277379118639315117)
                  ·
                    refine ⟨101250854017169489743169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 270002277379118639315117 101250854017169489743169)
                    ·
                      refine ⟨75938140512877117307377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 101250854017169489743169 75938140512877117307377)
                      ·
                        rfl

theorem cell23_147889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_147889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147889 prefixEnd_147889 := by exact prefixLift 147889
  have htrace : WordTrace (prefixWord ++ tailWord_147889) baseStart_147889 baseEnd_147889 := by
    simpa [prefixWord, tailWord_147889, baseEnd_147889] using wordTrace_append hprefix tailTrace_147889
  have hstable : (prefixWord ++ tailWord_147889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147889).length < 2 ^ (prefixWord ++ tailWord_147889).sum := by decide
  have hdescent : baseEnd_147889 < baseStart_147889 := by decide
  rcases family_descends (prefixWord ++ tailWord_147889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147955 : List Nat := [1, 1, 1, 2, 2, 2, 3, 3, 1, 7]
def baseStart_147955 : Nat := 118140960795 + 147955 * 2 ^ 59
def prefixEnd_147955 : Nat := 4983230072969 + 3 ^ 40 * 147955 * 2
def baseEnd_147955 : Nat := 25324010078691286360691

theorem tailTrace_147955 : CollatzResearch.WordTrace tailWord_147955 prefixEnd_147955 25324010078691286360691 := by
  unfold tailWord_147955
  simp only [CollatzResearch.WordTrace]
  refine ⟨5396362178991778547365319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3597574785994519031576879 5396362178991778547365319)
  ·
    refine ⟨8094543268487667821047979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5396362178991778547365319 8094543268487667821047979)
    ·
      refine ⟨12141814902731501731571969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8094543268487667821047979 12141814902731501731571969)
      ·
        refine ⟨9106361177048626298678977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12141814902731501731571969 9106361177048626298678977)
        ·
          refine ⟨6829770882786469724009233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9106361177048626298678977 6829770882786469724009233)
          ·
            refine ⟨5122328162089852293006925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6829770882786469724009233 5122328162089852293006925)
            ·
              refine ⟨1920873060783694609877597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5122328162089852293006925 1920873060783694609877597)
              ·
                refine ⟨720327397793885478704099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1920873060783694609877597 720327397793885478704099)
                ·
                  refine ⟨1080491096690828218056149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 720327397793885478704099 1080491096690828218056149)
                  ·
                    refine ⟨25324010078691286360691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1080491096690828218056149 25324010078691286360691)
                    ·
                      rfl

theorem cell23_147955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 7].length) (baseStart_147955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147955 prefixEnd_147955 := by exact prefixLift 147955
  have htrace : WordTrace (prefixWord ++ tailWord_147955) baseStart_147955 baseEnd_147955 := by
    simpa [prefixWord, tailWord_147955, baseEnd_147955] using wordTrace_append hprefix tailTrace_147955
  have hstable : (prefixWord ++ tailWord_147955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147955).length < 2 ^ (prefixWord ++ tailWord_147955).sum := by decide
  have hdescent : baseEnd_147955 < baseStart_147955 := by decide
  rcases family_descends (prefixWord ++ tailWord_147955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147982 : List Nat := [4, 1, 1, 2, 3, 1, 1, 1, 1, 1, 7]
def baseStart_147982 : Nat := 118140960795 + 147982 * 2 ^ 59
def prefixEnd_147982 : Nat := 4983230072969 + 3 ^ 40 * 147982 * 2
def baseEnd_147982 : Nat := 75985894213745253444449

theorem tailTrace_147982 : CollatzResearch.WordTrace tailWord_147982 prefixEnd_147982 75985894213745253444449 := by
  unfold tailWord_147982
  simp only [CollatzResearch.WordTrace]
  refine ⟨674668368736745269824775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3598231299929308105732133 674668368736745269824775)
  ·
    refine ⟨1012002553105117904737163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 674668368736745269824775 1012002553105117904737163)
    ·
      refine ⟨1518003829657676857105745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1012002553105117904737163 1518003829657676857105745)
      ·
        refine ⟨1138502872243257642829309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1518003829657676857105745 1138502872243257642829309)
        ·
          refine ⟨426938577091221616060991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1138502872243257642829309 426938577091221616060991)
          ·
            refine ⟨640407865636832424091487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 426938577091221616060991 640407865636832424091487)
            ·
              refine ⟨960611798455248636137231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 640407865636832424091487 960611798455248636137231)
              ·
                refine ⟨1440917697682872954205847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 960611798455248636137231 1440917697682872954205847)
                ·
                  refine ⟨2161376546524309431308771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1440917697682872954205847 2161376546524309431308771)
                  ·
                    refine ⟨3242064819786464146963157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2161376546524309431308771 3242064819786464146963157)
                    ·
                      refine ⟨75985894213745253444449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 3242064819786464146963157 75985894213745253444449)
                      ·
                        rfl

theorem cell23_147982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_147982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147982 prefixEnd_147982 := by exact prefixLift 147982
  have htrace : WordTrace (prefixWord ++ tailWord_147982) baseStart_147982 baseEnd_147982 := by
    simpa [prefixWord, tailWord_147982, baseEnd_147982] using wordTrace_append hprefix tailTrace_147982
  have hstable : (prefixWord ++ tailWord_147982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147982).length < 2 ^ (prefixWord ++ tailWord_147982).sum := by decide
  have hdescent : baseEnd_147982 < baseStart_147982 := by decide
  rcases family_descends (prefixWord ++ tailWord_147982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147985 : List Nat := [1, 2, 2, 1, 1, 2, 2, 2, 2, 8]
def baseStart_147985 : Nat := 118140960795 + 147985 * 2 ^ 59
def prefixEnd_147985 : Nat := 4983230072969 + 3 ^ 40 * 147985 * 2
def baseEnd_147985 : Nat := 25329144885236247235645

theorem tailTrace_147985 : CollatzResearch.WordTrace tailWord_147985 prefixEnd_147985 25329144885236247235645 := by
  unfold tailWord_147985
  simp only [CollatzResearch.WordTrace]
  refine ⟨5397456368883093670957409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3598304245922062447304939 5397456368883093670957409)
  ·
    refine ⟨4048092276662320253218057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5397456368883093670957409 4048092276662320253218057)
    ·
      refine ⟨3036069207496740189913543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4048092276662320253218057 3036069207496740189913543)
      ·
        refine ⟨4554103811245110284870315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3036069207496740189913543 4554103811245110284870315)
        ·
          refine ⟨6831155716867665427305473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4554103811245110284870315 6831155716867665427305473)
          ·
            refine ⟨5123366787650749070479105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6831155716867665427305473 5123366787650749070479105)
            ·
              refine ⟨3842525090738061802859329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5123366787650749070479105 3842525090738061802859329)
              ·
                refine ⟨2881893818053546352144497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3842525090738061802859329 2881893818053546352144497)
                ·
                  refine ⟨2161420363540159764108373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2881893818053546352144497 2161420363540159764108373)
                  ·
                    refine ⟨25329144885236247235645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 2161420363540159764108373 25329144885236247235645)
                    ·
                      rfl

theorem cell23_147985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 8].length) (baseStart_147985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147985 prefixEnd_147985 := by exact prefixLift 147985
  have htrace : WordTrace (prefixWord ++ tailWord_147985) baseStart_147985 baseEnd_147985 := by
    simpa [prefixWord, tailWord_147985, baseEnd_147985] using wordTrace_append hprefix tailTrace_147985
  have hstable : (prefixWord ++ tailWord_147985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147985).length < 2 ^ (prefixWord ++ tailWord_147985).sum := by decide
  have hdescent : baseEnd_147985 < baseStart_147985 := by decide
  rcases family_descends (prefixWord ++ tailWord_147985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147995 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 5]
def baseStart_147995 : Nat := 118140960795 + 147995 * 2 ^ 59
def prefixEnd_147995 : Nat := 4983230072969 + 3 ^ 40 * 147995 * 2
def baseEnd_147995 : Nat := 75992569462253702581889

theorem tailTrace_147995 : CollatzResearch.WordTrace tailWord_147995 prefixEnd_147995 75992569462253702581889 := by
  unfold tailWord_147995
  simp only [CollatzResearch.WordTrace]
  refine ⟨5397821098846865378821439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3598547399231243585880959 5397821098846865378821439)
  ·
    refine ⟨8096731648270298068232159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5397821098846865378821439 8096731648270298068232159)
    ·
      refine ⟨12145097472405447102348239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8096731648270298068232159 12145097472405447102348239)
      ·
        refine ⟨18217646208608170653522359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12145097472405447102348239 18217646208608170653522359)
        ·
          refine ⟨27326469312912255980283539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18217646208608170653522359 27326469312912255980283539)
          ·
            refine ⟨40989703969368383970425309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27326469312912255980283539 40989703969368383970425309)
            ·
              refine ⟨15371138988513143988909491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40989703969368383970425309 15371138988513143988909491)
              ·
                refine ⟨23056708482769715983364237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15371138988513143988909491 23056708482769715983364237)
                ·
                  refine ⟨8646265681038643493761589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23056708482769715983364237 8646265681038643493761589)
                  ·
                    refine ⟨810587407597372827540149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8646265681038643493761589 810587407597372827540149)
                    ·
                      refine ⟨75992569462253702581889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 810587407597372827540149 75992569462253702581889)
                      ·
                        rfl

theorem cell23_147995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 5].length) (baseStart_147995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_147995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_147995 prefixEnd_147995 := by exact prefixLift 147995
  have htrace : WordTrace (prefixWord ++ tailWord_147995) baseStart_147995 baseEnd_147995 := by
    simpa [prefixWord, tailWord_147995, baseEnd_147995] using wordTrace_append hprefix tailTrace_147995
  have hstable : (prefixWord ++ tailWord_147995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147995).length < 2 ^ (prefixWord ++ tailWord_147995).sum := by decide
  have hdescent : baseEnd_147995 < baseStart_147995 := by decide
  rcases family_descends (prefixWord ++ tailWord_147995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148012 : List Nat := [2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 3]
def baseStart_148012 : Nat := 118140960795 + 148012 * 2 ^ 59
def prefixEnd_148012 : Nat := 4983230072969 + 3 ^ 40 * 148012 * 2
def baseEnd_148012 : Nat := 76001298633380136069311

theorem tailTrace_148012 : CollatzResearch.WordTrace tailWord_148012 prefixEnd_148012 76001298633380136069311 := by
  unfold tailWord_148012
  simp only [CollatzResearch.WordTrace]
  refine ⟨2699220569892638641095145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3598960759856851521460193 2699220569892638641095145)
  ·
    refine ⟨2024415427419478980821359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2699220569892638641095145 2024415427419478980821359)
    ·
      refine ⟨3036623141129218471232039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2024415427419478980821359 3036623141129218471232039)
      ·
        refine ⟨4554934711693827706848059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3036623141129218471232039 4554934711693827706848059)
        ·
          refine ⟨6832402067540741560272089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4554934711693827706848059 6832402067540741560272089)
          ·
            refine ⟨5124301550655556170204067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6832402067540741560272089 5124301550655556170204067)
            ·
              refine ⟨7686452325983334255306101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5124301550655556170204067 7686452325983334255306101)
              ·
                refine ⟨720604905560937586434947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7686452325983334255306101 720604905560937586434947)
                ·
                  refine ⟨1080907358341406379652421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 720604905560937586434947 1080907358341406379652421)
                  ·
                    refine ⟨202670129689013696184829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1080907358341406379652421 202670129689013696184829)
                    ·
                      refine ⟨76001298633380136069311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 202670129689013696184829 76001298633380136069311)
                      ·
                        rfl

theorem cell23_148012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 3].length) (baseStart_148012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_148012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_148012 prefixEnd_148012 := by exact prefixLift 148012
  have htrace : WordTrace (prefixWord ++ tailWord_148012) baseStart_148012 baseEnd_148012 := by
    simpa [prefixWord, tailWord_148012, baseEnd_148012] using wordTrace_append hprefix tailTrace_148012
  have hstable : (prefixWord ++ tailWord_148012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148012).length < 2 ^ (prefixWord ++ tailWord_148012).sum := by decide
  have hdescent : baseEnd_148012 < baseStart_148012 := by decide
  rcases family_descends (prefixWord ++ tailWord_148012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148032 : List Nat := [2, 1, 1, 2, 2, 2, 3, 4, 6]
def baseStart_148032 : Nat := 118140960795 + 148032 * 2 ^ 59
def prefixEnd_148032 : Nat := 4983230072969 + 3 ^ 40 * 148032 * 2
def baseEnd_148032 : Nat := 8445729805163339757691

theorem tailTrace_148032 : CollatzResearch.WordTrace tailWord_148032 prefixEnd_148032 8445729805163339757691 := by
  unfold tailWord_148032
  simp only [CollatzResearch.WordTrace]
  refine ⟨2699585299856410348959175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3599447066475213798612233 2699585299856410348959175)
  ·
    refine ⟨4049377949784615523438763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2699585299856410348959175 4049377949784615523438763)
    ·
      refine ⟨6074066924676923285158145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4049377949784615523438763 6074066924676923285158145)
      ·
        refine ⟨4555550193507692463868609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6074066924676923285158145 4555550193507692463868609)
        ·
          refine ⟨3416662645130769347901457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4555550193507692463868609 3416662645130769347901457)
          ·
            refine ⟨2562496983848077010926093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3416662645130769347901457 2562496983848077010926093)
            ·
              refine ⟨960936368943028879097285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2562496983848077010926093 960936368943028879097285)
              ·
                refine ⟨180175569176817914830741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 960936368943028879097285 180175569176817914830741)
                ·
                  refine ⟨8445729805163339757691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 180175569176817914830741 8445729805163339757691)
                  ·
                    rfl

theorem cell23_148032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 4, 6].length) (baseStart_148032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_148032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_148032 prefixEnd_148032 := by exact prefixLift 148032
  have htrace : WordTrace (prefixWord ++ tailWord_148032) baseStart_148032 baseEnd_148032 := by
    simpa [prefixWord, tailWord_148032, baseEnd_148032] using wordTrace_append hprefix tailTrace_148032
  have hstable : (prefixWord ++ tailWord_148032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148032).length < 2 ^ (prefixWord ++ tailWord_148032).sum := by decide
  have hdescent : baseEnd_148032 < baseStart_148032 := by decide
  rcases family_descends (prefixWord ++ tailWord_148032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148092 : List Nat := [2, 2, 2, 1, 1, 2, 2, 2, 3, 6]
def baseStart_148092 : Nat := 118140960795 + 148092 * 2 ^ 59
def prefixEnd_148092 : Nat := 4983230072969 + 3 ^ 40 * 148092 * 2
def baseEnd_148092 : Nat := 25347459028579941022981

theorem tailTrace_148092 : CollatzResearch.WordTrace tailWord_148092 prefixEnd_148092 25347459028579941022981 := by
  unfold tailWord_148092
  simp only [CollatzResearch.WordTrace]
  refine ⟨2700679489747725472551265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3600905986330300630068353 2700679489747725472551265)
  ·
    refine ⟨2025509617310794104413449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2700679489747725472551265 2025509617310794104413449)
    ·
      refine ⟨1519132212983095578310087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2025509617310794104413449 1519132212983095578310087)
      ·
        refine ⟨2278698319474643367465131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1519132212983095578310087 2278698319474643367465131)
        ·
          refine ⟨3418047479211965051197697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2278698319474643367465131 3418047479211965051197697)
          ·
            refine ⟨2563535609408973788398273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3418047479211965051197697 2563535609408973788398273)
            ·
              refine ⟨1922651707056730341298705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2563535609408973788398273 1922651707056730341298705)
              ·
                refine ⟨1441988780292547755974029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1922651707056730341298705 1441988780292547755974029)
                ·
                  refine ⟨540745792609705408490261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1441988780292547755974029 540745792609705408490261)
                  ·
                    refine ⟨25347459028579941022981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 540745792609705408490261 25347459028579941022981)
                    ·
                      rfl

theorem cell23_148092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 3, 6].length) (baseStart_148092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_148092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_148092 prefixEnd_148092 := by exact prefixLift 148092
  have htrace : WordTrace (prefixWord ++ tailWord_148092) baseStart_148092 baseEnd_148092 := by
    simpa [prefixWord, tailWord_148092, baseEnd_148092] using wordTrace_append hprefix tailTrace_148092
  have hstable : (prefixWord ++ tailWord_148092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148092).length < 2 ^ (prefixWord ++ tailWord_148092).sum := by decide
  have hdescent : baseEnd_148092 < baseStart_148092 := by decide
  rcases family_descends (prefixWord ++ tailWord_148092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148093 : List Nat := [1, 4, 1, 1, 5, 1, 2, 1, 3, 1, 3]
def baseStart_148093 : Nat := 118140960795 + 148093 * 2 ^ 59
def prefixEnd_148093 : Nat := 4983230072969 + 3 ^ 40 * 148093 * 2
def baseEnd_148093 : Nat := 76042890566394319156439

theorem tailTrace_148093 : CollatzResearch.WordTrace tailWord_148093 prefixEnd_148093 76042890566394319156439 := by
  unfold tailWord_148093
  simp only [CollatzResearch.WordTrace]
  refine ⟨5401395452491828115888933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3600930301661218743925955 5401395452491828115888933)
  ·
    refine ⟨1012761647342217771729175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5401395452491828115888933 1012761647342217771729175)
    ·
      refine ⟨1519142471013326657593763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1012761647342217771729175 1519142471013326657593763)
      ·
        refine ⟨2278713706519989986390645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1519142471013326657593763 2278713706519989986390645)
        ·
          refine ⟨213629409986249061224123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2278713706519989986390645 213629409986249061224123)
          ·
            refine ⟨320444114979373591836185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213629409986249061224123 320444114979373591836185)
            ·
              refine ⟨240333086234530193877139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 320444114979373591836185 240333086234530193877139)
              ·
                refine ⟨360499629351795290815709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 240333086234530193877139 360499629351795290815709)
                ·
                  refine ⟨135187361006923234055891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 360499629351795290815709 135187361006923234055891)
                  ·
                    refine ⟨202781041510384851083837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 135187361006923234055891 202781041510384851083837)
                    ·
                      refine ⟨76042890566394319156439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 202781041510384851083837 76042890566394319156439)
                      ·
                        rfl

theorem cell23_148093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 3, 1, 3].length) (baseStart_148093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_148093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_148093 prefixEnd_148093 := by exact prefixLift 148093
  have htrace : WordTrace (prefixWord ++ tailWord_148093) baseStart_148093 baseEnd_148093 := by
    simpa [prefixWord, tailWord_148093, baseEnd_148093] using wordTrace_append hprefix tailTrace_148093
  have hstable : (prefixWord ++ tailWord_148093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148093).length < 2 ^ (prefixWord ++ tailWord_148093).sum := by decide
  have hdescent : baseEnd_148093 < baseStart_148093 := by decide
  rcases family_descends (prefixWord ++ tailWord_148093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148126 : List Nat := [4, 3, 1, 1, 1, 1, 1, 1, 6, 4]
def baseStart_148126 : Nat := 118140960795 + 148126 * 2 ^ 59
def prefixEnd_148126 : Nat := 4983230072969 + 3 ^ 40 * 148126 * 2
def baseEnd_148126 : Nat := 25353278475997563347929

theorem tailTrace_148126 : CollatzResearch.WordTrace tailWord_148126 prefixEnd_148126 25353278475997563347929 := by
  unfold tailWord_148126
  simp only [CollatzResearch.WordTrace]
  refine ⟨675324882671534343980029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3601732707581516501226821 675324882671534343980029)
  ·
    refine ⟨253246831001825378992511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 675324882671534343980029 253246831001825378992511)
    ·
      refine ⟨379870246502738068488767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253246831001825378992511 379870246502738068488767)
      ·
        refine ⟨569805369754107102733151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379870246502738068488767 569805369754107102733151)
        ·
          refine ⟨854708054631160654099727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 569805369754107102733151 854708054631160654099727)
          ·
            refine ⟨1282062081946740981149591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 854708054631160654099727 1282062081946740981149591)
            ·
              refine ⟨1923093122920111471724387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1282062081946740981149591 1923093122920111471724387)
              ·
                refine ⟨2884639684380167207586581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1923093122920111471724387 2884639684380167207586581)
                ·
                  refine ⟨135217485205320337855621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2884639684380167207586581 135217485205320337855621)
                  ·
                    refine ⟨25353278475997563347929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 135217485205320337855621 25353278475997563347929)
                    ·
                      rfl

theorem cell23_148126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_148126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_148126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_148126 prefixEnd_148126 := by exact prefixLift 148126
  have htrace : WordTrace (prefixWord ++ tailWord_148126) baseStart_148126 baseEnd_148126 := by
    simpa [prefixWord, tailWord_148126, baseEnd_148126] using wordTrace_append hprefix tailTrace_148126
  have hstable : (prefixWord ++ tailWord_148126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148126).length < 2 ^ (prefixWord ++ tailWord_148126).sum := by decide
  have hdescent : baseEnd_148126 < baseStart_148126 := by decide
  rcases family_descends (prefixWord ++ tailWord_148126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148200 : List Nat := [2, 1, 4, 1, 4, 1, 2, 2, 2, 1, 3]
def baseStart_148200 : Nat := 118140960795 + 148200 * 2 ^ 59
def prefixEnd_148200 : Nat := 4983230072969 + 3 ^ 40 * 148200 * 2
def baseEnd_148200 : Nat := 76097832996425400518447

theorem tailTrace_148200 : CollatzResearch.WordTrace tailWord_148200 prefixEnd_148200 76097832996425400518447 := by
  unfold tailWord_148200
  simp only [CollatzResearch.WordTrace]
  refine ⟨2702649031552092695017027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3603532042069456926689369 2702649031552092695017027)
  ·
    refine ⟨4053973547328139042525541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2702649031552092695017027 4053973547328139042525541)
    ·
      refine ⟨760120040124026070473539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4053973547328139042525541 760120040124026070473539)
      ·
        refine ⟨1140180060186039105710309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 760120040124026070473539 1140180060186039105710309)
        ·
          refine ⟨213783761284882332320683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1140180060186039105710309 213783761284882332320683)
          ·
            refine ⟨320675641927323498481025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213783761284882332320683 320675641927323498481025)
            ·
              refine ⟨240506731445492623860769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 320675641927323498481025 240506731445492623860769)
              ·
                refine ⟨180380048584119467895577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 240506731445492623860769 180380048584119467895577)
                ·
                  refine ⟨135285036438089600921683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 180380048584119467895577 135285036438089600921683)
                  ·
                    refine ⟨202927554657134401382525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 135285036438089600921683 202927554657134401382525)
                    ·
                      refine ⟨76097832996425400518447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 202927554657134401382525 76097832996425400518447)
                      ·
                        rfl

theorem cell23_148200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_148200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_148200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_148200 prefixEnd_148200 := by exact prefixLift 148200
  have htrace : WordTrace (prefixWord ++ tailWord_148200) baseStart_148200 baseEnd_148200 := by
    simpa [prefixWord, tailWord_148200, baseEnd_148200] using wordTrace_append hprefix tailTrace_148200
  have hstable : (prefixWord ++ tailWord_148200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148200).length < 2 ^ (prefixWord ++ tailWord_148200).sum := by decide
  have hdescent : baseEnd_148200 < baseStart_148200 := by decide
  rcases family_descends (prefixWord ++ tailWord_148200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148209 : List Nat := [1, 2, 2, 2, 2, 2, 1, 1, 1, 6, 3]
def baseStart_148209 : Nat := 118140960795 + 148209 * 2 ^ 59
def prefixEnd_148209 : Nat := 4983230072969 + 3 ^ 40 * 148209 * 2
def baseEnd_148209 : Nat := 76102454322315865305905

theorem tailTrace_148209 : CollatzResearch.WordTrace tailWord_148209 prefixEnd_148209 76102454322315865305905 := by
  unfold tailWord_148209
  simp only [CollatzResearch.WordTrace]
  refine ⟨5405626320071579927111681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3603750880047719951407787 5405626320071579927111681)
  ·
    refine ⟨4054219740053684945333761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5405626320071579927111681 4054219740053684945333761)
    ·
      refine ⟨3040664805040263709000321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4054219740053684945333761 3040664805040263709000321)
      ·
        refine ⟨2280498603780197781750241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3040664805040263709000321 2280498603780197781750241)
        ·
          refine ⟨1710373952835148336312681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2280498603780197781750241 1710373952835148336312681)
          ·
            refine ⟨1282780464626361252234511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1710373952835148336312681 1282780464626361252234511)
            ·
              refine ⟨1924170696939541878351767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1282780464626361252234511 1924170696939541878351767)
              ·
                refine ⟨2886256045409312817527651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1924170696939541878351767 2886256045409312817527651)
                ·
                  refine ⟨4329384068113969226291477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2886256045409312817527651 4329384068113969226291477)
                  ·
                    refine ⟨202939878192842307482413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4329384068113969226291477 202939878192842307482413)
                    ·
                      refine ⟨76102454322315865305905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 202939878192842307482413 76102454322315865305905)
                      ·
                        rfl

theorem cell23_148209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 6, 3].length) (baseStart_148209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_148209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_148209 prefixEnd_148209 := by exact prefixLift 148209
  have htrace : WordTrace (prefixWord ++ tailWord_148209) baseStart_148209 baseEnd_148209 := by
    simpa [prefixWord, tailWord_148209, baseEnd_148209] using wordTrace_append hprefix tailTrace_148209
  have hstable : (prefixWord ++ tailWord_148209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148209).length < 2 ^ (prefixWord ++ tailWord_148209).sum := by decide
  have hdescent : baseEnd_148209 < baseStart_148209 := by decide
  rcases family_descends (prefixWord ++ tailWord_148209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148239 : List Nat := [1, 1, 2, 1, 1, 1, 5, 2, 1, 5, 3]
def baseStart_148239 : Nat := 118140960795 + 148239 * 2 ^ 59
def prefixEnd_148239 : Nat := 4983230072969 + 3 ^ 40 * 148239 * 2
def baseEnd_148239 : Nat := 76117858741950747930767

theorem tailTrace_148239 : CollatzResearch.WordTrace tailWord_148239 prefixEnd_148239 76117858741950747930767 := by
  unfold tailWord_148239
  simp only [CollatzResearch.WordTrace]
  refine ⟨5406720509962895050703771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3604480339975263367135847 5406720509962895050703771)
  ·
    refine ⟨8110080764944342576055657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5406720509962895050703771 8110080764944342576055657)
    ·
      refine ⟨6082560573708256932041743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8110080764944342576055657 6082560573708256932041743)
      ·
        refine ⟨9123840860562385398062615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6082560573708256932041743 9123840860562385398062615)
        ·
          refine ⟨13685761290843578097093923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9123840860562385398062615 13685761290843578097093923)
          ·
            refine ⟨20528641936265367145640885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13685761290843578097093923 20528641936265367145640885)
            ·
              refine ⟨1924560181524878169903833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20528641936265367145640885 1924560181524878169903833)
              ·
                refine ⟨1443420136143658627427875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1924560181524878169903833 1443420136143658627427875)
                ·
                  refine ⟨2165130204215487941141813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1443420136143658627427875 2165130204215487941141813)
                  ·
                    refine ⟨202980956645201994482045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2165130204215487941141813 202980956645201994482045)
                    ·
                      refine ⟨76117858741950747930767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 202980956645201994482045 76117858741950747930767)
                      ·
                        rfl

theorem cell23_148239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 5, 3].length) (baseStart_148239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_148239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_148239 prefixEnd_148239 := by exact prefixLift 148239
  have htrace : WordTrace (prefixWord ++ tailWord_148239) baseStart_148239 baseEnd_148239 := by
    simpa [prefixWord, tailWord_148239, baseEnd_148239] using wordTrace_append hprefix tailTrace_148239
  have hstable : (prefixWord ++ tailWord_148239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148239).length < 2 ^ (prefixWord ++ tailWord_148239).sum := by decide
  have hdescent : baseEnd_148239 < baseStart_148239 := by decide
  rcases family_descends (prefixWord ++ tailWord_148239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148256 : List Nat := [2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 3]
def baseStart_148256 : Nat := 118140960795 + 148256 * 2 ^ 59
def prefixEnd_148256 : Nat := 4983230072969 + 3 ^ 40 * 148256 * 2
def baseEnd_148256 : Nat := 76126587913077181418189

theorem tailTrace_148256 : CollatzResearch.WordTrace tailWord_148256 prefixEnd_148256 76126587913077181418189 := by
  unfold tailWord_148256
  simp only [CollatzResearch.WordTrace]
  refine ⟨2703670275450653477036311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3604893700600871302715081 2703670275450653477036311)
  ·
    refine ⟨4055505413175980215554467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2703670275450653477036311 4055505413175980215554467)
    ·
      refine ⟨6083258119763970323331701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4055505413175980215554467 6083258119763970323331701)
      ·
        refine ⟨570305448727872217812347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6083258119763970323331701 570305448727872217812347)
        ·
          refine ⟨855458173091808326718521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 570305448727872217812347 855458173091808326718521)
          ·
            refine ⟨641593629818856245038891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 855458173091808326718521 641593629818856245038891)
            ·
              refine ⟨962390444728284367558337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 641593629818856245038891 962390444728284367558337)
              ·
                refine ⟨721792833546213275668753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 962390444728284367558337 721792833546213275668753)
                ·
                  refine ⟨541344625159659956751565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 721792833546213275668753 541344625159659956751565)
                  ·
                    refine ⟨203004234434872483781837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 541344625159659956751565 203004234434872483781837)
                    ·
                      refine ⟨76126587913077181418189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 203004234434872483781837 76126587913077181418189)
                      ·
                        rfl

theorem cell23_148256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_148256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_148256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_148256 prefixEnd_148256 := by exact prefixLift 148256
  have htrace : WordTrace (prefixWord ++ tailWord_148256) baseStart_148256 baseEnd_148256 := by
    simpa [prefixWord, tailWord_148256, baseEnd_148256] using wordTrace_append hprefix tailTrace_148256
  have hstable : (prefixWord ++ tailWord_148256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148256).length < 2 ^ (prefixWord ++ tailWord_148256).sum := by decide
  have hdescent : baseEnd_148256 < baseStart_148256 := by decide
  rcases family_descends (prefixWord ++ tailWord_148256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148259 : List Nat := [1, 1, 1, 4, 2, 1, 1, 3, 4, 5]
def baseStart_148259 : Nat := 118140960795 + 148259 * 2 ^ 59
def prefixEnd_148259 : Nat := 4983230072969 + 3 ^ 40 * 148259 * 2
def baseEnd_148259 : Nat := 25376042785013556560225

theorem tailTrace_148259 : CollatzResearch.WordTrace tailWord_148259 prefixEnd_148259 25376042785013556560225 := by
  unfold tailWord_148259
  simp only [CollatzResearch.WordTrace]
  refine ⟨5407449969890438466431831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3604966646593625644287887 5407449969890438466431831)
  ·
    refine ⟨8111174954835657699647747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5407449969890438466431831 8111174954835657699647747)
    ·
      refine ⟨12166762432253486549471621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8111174954835657699647747 12166762432253486549471621)
      ·
        refine ⟨2281267956047528728025929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12166762432253486549471621 2281267956047528728025929)
        ·
          refine ⟨1710950967035646546019447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2281267956047528728025929 1710950967035646546019447)
          ·
            refine ⟨2566426450553469819029171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1710950967035646546019447 2566426450553469819029171)
            ·
              refine ⟨3849639675830204728543757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2566426450553469819029171 3849639675830204728543757)
              ·
                refine ⟨1443614878436326773203909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3849639675830204728543757 1443614878436326773203909)
                ·
                  refine ⟨270677789706811269975733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1443614878436326773203909 270677789706811269975733)
                  ·
                    refine ⟨25376042785013556560225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 270677789706811269975733 25376042785013556560225)
                    ·
                      rfl

theorem cell23_148259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 4, 5].length) (baseStart_148259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_148259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_148259 prefixEnd_148259 := by exact prefixLift 148259
  have htrace : WordTrace (prefixWord ++ tailWord_148259) baseStart_148259 baseEnd_148259 := by
    simpa [prefixWord, tailWord_148259, baseEnd_148259] using wordTrace_append hprefix tailTrace_148259
  have hstable : (prefixWord ++ tailWord_148259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148259).length < 2 ^ (prefixWord ++ tailWord_148259).sum := by decide
  have hdescent : baseEnd_148259 < baseStart_148259 := by decide
  rcases family_descends (prefixWord ++ tailWord_148259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148279 : List Nat := [1, 1, 3, 1, 2, 1, 3, 1, 3, 3, 4]
def baseStart_148279 : Nat := 118140960795 + 148279 * 2 ^ 59
def prefixEnd_148279 : Nat := 4983230072969 + 3 ^ 40 * 148279 * 2
def baseEnd_148279 : Nat := 76138397968130591430583

theorem tailTrace_148279 : CollatzResearch.WordTrace tailWord_148279 prefixEnd_148279 76138397968130591430583 := by
  unfold tailWord_148279
  simp only [CollatzResearch.WordTrace]
  refine ⟨5408179429817981882159891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3605452953211987921439927 5408179429817981882159891)
  ·
    refine ⟨8112269144726972823239837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5408179429817981882159891 8112269144726972823239837)
    ·
      refine ⟨3042100929272614808714939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8112269144726972823239837 3042100929272614808714939)
      ·
        refine ⟨4563151393908922213072409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3042100929272614808714939 4563151393908922213072409)
        ·
          refine ⟨3422363545431691659804307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4563151393908922213072409 3422363545431691659804307)
          ·
            refine ⟨5133545318147537489706461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3422363545431691659804307 5133545318147537489706461)
            ·
              refine ⟨1925079494305326558639923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5133545318147537489706461 1925079494305326558639923)
              ·
                refine ⟨2887619241457989837959885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1925079494305326558639923 2887619241457989837959885)
                ·
                  refine ⟨1082857215546746189234957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2887619241457989837959885 1082857215546746189234957)
                  ·
                    refine ⟨406071455830029820963109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1082857215546746189234957 406071455830029820963109)
                    ·
                      refine ⟨76138397968130591430583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 406071455830029820963109 76138397968130591430583)
                      ·
                        rfl

theorem cell23_148279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 3, 4].length) (baseStart_148279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_148279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_148279 prefixEnd_148279 := by exact prefixLift 148279
  have htrace : WordTrace (prefixWord ++ tailWord_148279) baseStart_148279 baseEnd_148279 := by
    simpa [prefixWord, tailWord_148279, baseEnd_148279] using wordTrace_append hprefix tailTrace_148279
  have hstable : (prefixWord ++ tailWord_148279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148279).length < 2 ^ (prefixWord ++ tailWord_148279).sum := by decide
  have hdescent : baseEnd_148279 < baseStart_148279 := by decide
  rcases family_descends (prefixWord ++ tailWord_148279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148296 : List Nat := [2, 1, 3, 1, 1, 3, 2, 3, 2, 1, 4]
def baseStart_148296 : Nat := 118140960795 + 148296 * 2 ^ 59
def prefixEnd_148296 : Nat := 4983230072969 + 3 ^ 40 * 148296 * 2
def baseEnd_148296 : Nat := 76147127139257024918005

theorem tailTrace_148296 : CollatzResearch.WordTrace tailWord_148296 prefixEnd_148296 76147127139257024918005 := by
  unfold tailWord_148296
  simp only [CollatzResearch.WordTrace]
  refine ⟨2704399735378196892764371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3605866313837595857019161 2704399735378196892764371)
  ·
    refine ⟨4056599603067295339146557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2704399735378196892764371 4056599603067295339146557)
    ·
      refine ⟨1521224851150235752179959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4056599603067295339146557 1521224851150235752179959)
      ·
        refine ⟨2281837276725353628269939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1521224851150235752179959 2281837276725353628269939)
        ·
          refine ⟨3422755915088030442404909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2281837276725353628269939 3422755915088030442404909)
          ·
            refine ⟨1283533468158011415901841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3422755915088030442404909 1283533468158011415901841)
            ·
              refine ⟨962650101118508561926381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1283533468158011415901841 962650101118508561926381)
              ·
                refine ⟨360993787919440710722393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 962650101118508561926381 360993787919440710722393)
                ·
                  refine ⟨270745340939580533041795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 360993787919440710722393 270745340939580533041795)
                  ·
                    refine ⟨406118011409370799562693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 270745340939580533041795 406118011409370799562693)
                    ·
                      refine ⟨76147127139257024918005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 406118011409370799562693 76147127139257024918005)
                      ·
                        rfl

theorem cell23_148296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_148296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_148296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_148296 prefixEnd_148296 := by exact prefixLift 148296
  have htrace : WordTrace (prefixWord ++ tailWord_148296) baseStart_148296 baseEnd_148296 := by
    simpa [prefixWord, tailWord_148296, baseEnd_148296] using wordTrace_append hprefix tailTrace_148296
  have hstable : (prefixWord ++ tailWord_148296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148296).length < 2 ^ (prefixWord ++ tailWord_148296).sum := by decide
  have hdescent : baseEnd_148296 < baseStart_148296 := by decide
  rcases family_descends (prefixWord ++ tailWord_148296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148319 : List Nat := [1, 1, 2, 3, 1, 3, 1, 3, 8]
def baseStart_148319 : Nat := 118140960795 + 148319 * 2 ^ 59
def prefixEnd_148319 : Nat := 4983230072969 + 3 ^ 40 * 148319 * 2
def baseEnd_148319 : Nat := 8462104132701159436711

theorem tailTrace_148319 : CollatzResearch.WordTrace tailWord_148319 prefixEnd_148319 8462104132701159436711 := by
  unfold tailWord_148319
  simp only [CollatzResearch.WordTrace]
  refine ⟨5409638349673068713616011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3606425566448712475744007 5409638349673068713616011)
  ·
    refine ⟨8114457524509603070424017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5409638349673068713616011 8114457524509603070424017)
    ·
      refine ⟨6085843143382202302818013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8114457524509603070424017 6085843143382202302818013)
      ·
        refine ⟨2282191178768325863556755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6085843143382202302818013 2282191178768325863556755)
        ·
          refine ⟨3423286768152488795335133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2282191178768325863556755 3423286768152488795335133)
          ·
            refine ⟨1283732538057183298250675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3423286768152488795335133 1283732538057183298250675)
            ·
              refine ⟨1925598807085774947376013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1283732538057183298250675 1925598807085774947376013)
              ·
                refine ⟨722099552657165605266005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1925598807085774947376013 722099552657165605266005)
                ·
                  refine ⟨8462104132701159436711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 722099552657165605266005 8462104132701159436711)
                  ·
                    rfl

theorem cell23_148319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 8].length) (baseStart_148319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_148319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_148319 prefixEnd_148319 := by exact prefixLift 148319
  have htrace : WordTrace (prefixWord ++ tailWord_148319) baseStart_148319 baseEnd_148319 := by
    simpa [prefixWord, tailWord_148319, baseEnd_148319] using wordTrace_append hprefix tailTrace_148319
  have hstable : (prefixWord ++ tailWord_148319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148319).length < 2 ^ (prefixWord ++ tailWord_148319).sum := by decide
  have hdescent : baseEnd_148319 < baseStart_148319 := by decide
  rcases family_descends (prefixWord ++ tailWord_148319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148323 : List Nat := [1, 1, 1, 5, 3, 1, 3, 1, 3, 4]
def baseStart_148323 : Nat := 118140960795 + 148323 * 2 ^ 59
def prefixEnd_148323 : Nat := 4983230072969 + 3 ^ 40 * 148323 * 2
def baseEnd_148323 : Nat := 25386997038976139760127

theorem tailTrace_148323 : CollatzResearch.WordTrace tailWord_148323 prefixEnd_148323 25386997038976139760127 := by
  unfold tailWord_148323
  simp only [CollatzResearch.WordTrace]
  refine ⟨5409784241658577396761623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3606522827772384931174415 5409784241658577396761623)
  ·
    refine ⟨8114676362487866095142435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5409784241658577396761623 8114676362487866095142435)
    ·
      refine ⟨12172014543731799142713653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8114676362487866095142435 12172014543731799142713653)
      ·
        refine ⟨1141126363474856169629405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12172014543731799142713653 1141126363474856169629405)
        ·
          refine ⟨427922386303071063611027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1141126363474856169629405 427922386303071063611027)
          ·
            refine ⟨641883579454606595416541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 427922386303071063611027 641883579454606595416541)
            ·
              refine ⟨240706342295477473281203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 641883579454606595416541 240706342295477473281203)
              ·
                refine ⟨361059513443216209921805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 240706342295477473281203 361059513443216209921805)
                ·
                  refine ⟨135397317541206078720677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 361059513443216209921805 135397317541206078720677)
                  ·
                    refine ⟨25386997038976139760127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 135397317541206078720677 25386997038976139760127)
                    ·
                      rfl

theorem cell23_148323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 3, 4].length) (baseStart_148323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_148323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_148323 prefixEnd_148323 := by exact prefixLift 148323
  have htrace : WordTrace (prefixWord ++ tailWord_148323) baseStart_148323 baseEnd_148323 := by
    simpa [prefixWord, tailWord_148323, baseEnd_148323] using wordTrace_append hprefix tailTrace_148323
  have hstable : (prefixWord ++ tailWord_148323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148323).length < 2 ^ (prefixWord ++ tailWord_148323).sum := by decide
  have hdescent : baseEnd_148323 < baseStart_148323 := by decide
  rcases family_descends (prefixWord ++ tailWord_148323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148339 : List Nat := [1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 6]
def baseStart_148339 : Nat := 118140960795 + 148339 * 2 ^ 59
def prefixEnd_148339 : Nat := 4983230072969 + 3 ^ 40 * 148339 * 2
def baseEnd_148339 : Nat := 76169206807400356680307

theorem tailTrace_148339 : CollatzResearch.WordTrace tailWord_148339 prefixEnd_148339 76169206807400356680307 := by
  unfold tailWord_148339
  simp only [CollatzResearch.WordTrace]
  refine ⟨5410367809600612129344071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3606911873067074752896047 5410367809600612129344071)
  ·
    refine ⟨8115551714400918194016107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5410367809600612129344071 8115551714400918194016107)
    ·
      refine ⟨12173327571601377291024161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8115551714400918194016107 12173327571601377291024161)
      ·
        refine ⟨9129995678701032968268121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12173327571601377291024161 9129995678701032968268121)
        ·
          refine ⟨6847496759025774726201091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9129995678701032968268121 6847496759025774726201091)
          ·
            refine ⟨10271245138538662089301637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6847496759025774726201091 10271245138538662089301637)
            ·
              refine ⟨1925858463475999141744057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10271245138538662089301637 1925858463475999141744057)
              ·
                refine ⟨1444393847606999356308043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1925858463475999141744057 1444393847606999356308043)
                ·
                  refine ⟨2166590771410499034462065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1444393847606999356308043 2166590771410499034462065)
                  ·
                    refine ⟨1624943078557874275846549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2166590771410499034462065 1624943078557874275846549)
                    ·
                      refine ⟨76169206807400356680307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1624943078557874275846549 76169206807400356680307)
                      ·
                        rfl

theorem cell23_148339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 6].length) (baseStart_148339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_148339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_148339 prefixEnd_148339 := by exact prefixLift 148339
  have htrace : WordTrace (prefixWord ++ tailWord_148339) baseStart_148339 baseEnd_148339 := by
    simpa [prefixWord, tailWord_148339, baseEnd_148339] using wordTrace_append hprefix tailTrace_148339
  have hstable : (prefixWord ++ tailWord_148339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148339).length < 2 ^ (prefixWord ++ tailWord_148339).sum := by decide
  have hdescent : baseEnd_148339 < baseStart_148339 := by decide
  rcases family_descends (prefixWord ++ tailWord_148339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148370 : List Nat := [3, 2, 3, 2, 2, 1, 2, 2, 6]
def baseStart_148370 : Nat := 118140960795 + 148370 * 2 ^ 59
def prefixEnd_148370 : Nat := 4983230072969 + 3 ^ 40 * 148370 * 2
def baseEnd_148370 : Nat := 8465013856409970599185

theorem tailTrace_148370 : CollatzResearch.WordTrace tailWord_148370 prefixEnd_148370 8465013856409970599185 := by
  unfold tailWord_148370
  simp only [CollatzResearch.WordTrace]
  refine ⟨1352874618122076105930641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3607665648325536282481709 1352874618122076105930641)
  ·
    refine ⟨1014655963591557079447981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1352874618122076105930641 1014655963591557079447981)
    ·
      refine ⟨380495986346833904792993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1014655963591557079447981 380495986346833904792993)
      ·
        refine ⟨285371989760125428594745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 380495986346833904792993 285371989760125428594745)
        ·
          refine ⟨214028992320094071446059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 285371989760125428594745 214028992320094071446059)
          ·
            refine ⟨321043488480141107169089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214028992320094071446059 321043488480141107169089)
            ·
              refine ⟨240782616360105830376817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 321043488480141107169089 240782616360105830376817)
              ·
                refine ⟨180586962270079372782613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 240782616360105830376817 180586962270079372782613)
                ·
                  refine ⟨8465013856409970599185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 180586962270079372782613 8465013856409970599185)
                  ·
                    rfl

theorem cell23_148370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 2, 6].length) (baseStart_148370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_148370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_148370 prefixEnd_148370 := by exact prefixLift 148370
  have htrace : WordTrace (prefixWord ++ tailWord_148370) baseStart_148370 baseEnd_148370 := by
    simpa [prefixWord, tailWord_148370, baseEnd_148370] using wordTrace_append hprefix tailTrace_148370
  have hstable : (prefixWord ++ tailWord_148370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148370).length < 2 ^ (prefixWord ++ tailWord_148370).sum := by decide
  have hdescent : baseEnd_148370 < baseStart_148370 := by decide
  rcases family_descends (prefixWord ++ tailWord_148370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148430 : List Nat := [4, 1, 1, 1, 2, 3, 3, 2, 2, 4]
def baseStart_148430 : Nat := 118140960795 + 148430 * 2 ^ 59
def prefixEnd_148430 : Nat := 4983230072969 + 3 ^ 40 * 148430 * 2
def baseEnd_148430 : Nat := 25405311182319833547463

theorem tailTrace_148430 : CollatzResearch.WordTrace tailWord_148430 prefixEnd_148430 25405311182319833547463 := by
  unfold tailWord_148430
  simp only [CollatzResearch.WordTrace]
  refine ⟨676710856533866833863343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3609124568180623113937829 676710856533866833863343)
  ·
    refine ⟨1015066284800800250795015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 676710856533866833863343 1015066284800800250795015)
    ·
      refine ⟨1522599427201200376192523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1015066284800800250795015 1522599427201200376192523)
      ·
        refine ⟨2283899140801800564288785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1522599427201200376192523 2283899140801800564288785)
        ·
          refine ⟨1712924355601350423216589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2283899140801800564288785 1712924355601350423216589)
          ·
            refine ⟨642346633350506408706221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1712924355601350423216589 642346633350506408706221)
            ·
              refine ⟨240879987506439903264833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 642346633350506408706221 240879987506439903264833)
              ·
                refine ⟨180659990629829927448625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 240879987506439903264833 180659990629829927448625)
                ·
                  refine ⟨135494992972372445586469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 180659990629829927448625 135494992972372445586469)
                  ·
                    refine ⟨25405311182319833547463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 135494992972372445586469 25405311182319833547463)
                    ·
                      rfl

theorem cell23_148430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 2, 2, 4].length) (baseStart_148430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_148430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_148430 prefixEnd_148430 := by exact prefixLift 148430
  have htrace : WordTrace (prefixWord ++ tailWord_148430) baseStart_148430 baseEnd_148430 := by
    simpa [prefixWord, tailWord_148430, baseEnd_148430] using wordTrace_append hprefix tailTrace_148430
  have hstable : (prefixWord ++ tailWord_148430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148430).length < 2 ^ (prefixWord ++ tailWord_148430).sum := by decide
  have hdescent : baseEnd_148430 < baseStart_148430 := by decide
  rcases family_descends (prefixWord ++ tailWord_148430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148447 : List Nat := [1, 1, 2, 3, 5, 1, 3, 1, 2, 4]
def baseStart_148447 : Nat := 118140960795 + 148447 * 2 ^ 59
def prefixEnd_148447 : Nat := 4983230072969 + 3 ^ 40 * 148447 * 2
def baseEnd_148447 : Nat := 25408220906028644709937

theorem tailTrace_148447 : CollatzResearch.WordTrace tailWord_148447 prefixEnd_148447 25408220906028644709937 := by
  unfold tailWord_148447
  simp only [CollatzResearch.WordTrace]
  refine ⟨5414306893209346574275595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3609537928806231049517063 5414306893209346574275595)
  ·
    refine ⟨8121460339814019861413393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5414306893209346574275595 8121460339814019861413393)
    ·
      refine ⟨6091095254860514896060045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8121460339814019861413393 6091095254860514896060045)
      ·
        refine ⟨2284160720572693086022517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6091095254860514896060045 2284160720572693086022517)
        ·
          refine ⟨214140067553689976814611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2284160720572693086022517 214140067553689976814611)
          ·
            refine ⟨321210101330534965221917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214140067553689976814611 321210101330534965221917)
            ·
              refine ⟨120453787998950611958219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 321210101330534965221917 120453787998950611958219)
              ·
                refine ⟨180680681998425917937329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120453787998950611958219 180680681998425917937329)
                ·
                  refine ⟨135510511498819438452997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 180680681998425917937329 135510511498819438452997)
                  ·
                    refine ⟨25408220906028644709937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 135510511498819438452997 25408220906028644709937)
                    ·
                      rfl

theorem cell23_148447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 1, 2, 4].length) (baseStart_148447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_148447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_148447 prefixEnd_148447 := by exact prefixLift 148447
  have htrace : WordTrace (prefixWord ++ tailWord_148447) baseStart_148447 baseEnd_148447 := by
    simpa [prefixWord, tailWord_148447, baseEnd_148447] using wordTrace_append hprefix tailTrace_148447
  have hstable : (prefixWord ++ tailWord_148447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148447).length < 2 ^ (prefixWord ++ tailWord_148447).sum := by decide
  have hdescent : baseEnd_148447 < baseStart_148447 := by decide
  rcases family_descends (prefixWord ++ tailWord_148447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148450 : List Nat := [3, 3, 3, 1, 1, 2, 1, 1, 1, 1, 6]
def baseStart_148450 : Nat := 118140960795 + 148450 * 2 ^ 59
def prefixEnd_148450 : Nat := 4983230072969 + 3 ^ 40 * 148450 * 2
def baseEnd_148450 : Nat := 76226203160049422392297

theorem tailTrace_148450 : CollatzResearch.WordTrace tailWord_148450 prefixEnd_148450 76226203160049422392297 := by
  unfold tailWord_148450
  simp only [CollatzResearch.WordTrace]
  refine ⟨1353604078049619521658701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3609610874798985391089869 1353604078049619521658701)
  ·
    refine ⟨507601529268607320622013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1353604078049619521658701 507601529268607320622013)
    ·
      refine ⟨190350573475727745233255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 507601529268607320622013 190350573475727745233255)
      ·
        refine ⟨285525860213591617849883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190350573475727745233255 285525860213591617849883)
        ·
          refine ⟨428288790320387426774825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285525860213591617849883 428288790320387426774825)
          ·
            refine ⟨321216592740290570081119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 428288790320387426774825 321216592740290570081119)
            ·
              refine ⟨481824889110435855121679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 321216592740290570081119 481824889110435855121679)
              ·
                refine ⟨722737333665653782682519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 481824889110435855121679 722737333665653782682519)
                ·
                  refine ⟨1084106000498480674023779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 722737333665653782682519 1084106000498480674023779)
                  ·
                    refine ⟨1626159000747721011035669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1084106000498480674023779 1626159000747721011035669)
                    ·
                      refine ⟨76226203160049422392297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1626159000747721011035669 76226203160049422392297)
                      ·
                        rfl

theorem cell23_148450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_148450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_148450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_148450 prefixEnd_148450 := by exact prefixLift 148450
  have htrace : WordTrace (prefixWord ++ tailWord_148450) baseStart_148450 baseEnd_148450 := by
    simpa [prefixWord, tailWord_148450, baseEnd_148450] using wordTrace_append hprefix tailTrace_148450
  have hstable : (prefixWord ++ tailWord_148450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148450).length < 2 ^ (prefixWord ++ tailWord_148450).sum := by decide
  have hdescent : baseEnd_148450 < baseStart_148450 := by decide
  rcases family_descends (prefixWord ++ tailWord_148450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148456 : List Nat := [2, 1, 4, 1, 1, 1, 2, 2, 2, 7]
def baseStart_148456 : Nat := 118140960795 + 148456 * 2 ^ 59
def prefixEnd_148456 : Nat := 4983230072969 + 3 ^ 40 * 148456 * 2
def baseEnd_148456 : Nat := 25409761347992132972423

theorem tailTrace_148456 : CollatzResearch.WordTrace tailWord_148456 prefixEnd_148456 25409761347992132972423 := by
  unfold tailWord_148456
  simp only [CollatzResearch.WordTrace]
  refine ⟨2707317575088370555676611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3609756766784494074235481 2707317575088370555676611)
  ·
    refine ⟨4060976362632555833514917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2707317575088370555676611 4060976362632555833514917)
    ·
      refine ⟨761433067993604218784047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4060976362632555833514917 761433067993604218784047)
      ·
        refine ⟨1142149601990406328176071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 761433067993604218784047 1142149601990406328176071)
        ·
          refine ⟨1713224402985609492264107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1142149601990406328176071 1713224402985609492264107)
          ·
            refine ⟨2569836604478414238396161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1713224402985609492264107 2569836604478414238396161)
            ·
              refine ⟨1927377453358810678797121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2569836604478414238396161 1927377453358810678797121)
              ·
                refine ⟨1445533090019108009097841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1927377453358810678797121 1445533090019108009097841)
                ·
                  refine ⟨1084149817514331006823381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1445533090019108009097841 1084149817514331006823381)
                  ·
                    refine ⟨25409761347992132972423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1084149817514331006823381 25409761347992132972423)
                    ·
                      rfl

theorem cell23_148456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_148456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_148456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_148456 prefixEnd_148456 := by exact prefixLift 148456
  have htrace : WordTrace (prefixWord ++ tailWord_148456) baseStart_148456 baseEnd_148456 := by
    simpa [prefixWord, tailWord_148456, baseEnd_148456] using wordTrace_append hprefix tailTrace_148456
  have hstable : (prefixWord ++ tailWord_148456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148456).length < 2 ^ (prefixWord ++ tailWord_148456).sum := by decide
  have hdescent : baseEnd_148456 < baseStart_148456 := by decide
  rcases family_descends (prefixWord ++ tailWord_148456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148496 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 5]
def baseStart_148496 : Nat := 118140960795 + 148496 * 2 ^ 59
def prefixEnd_148496 : Nat := 4983230072969 + 3 ^ 40 * 148496 * 2
def baseEnd_148496 : Nat := 76249823270156242417085

theorem tailTrace_148496 : CollatzResearch.WordTrace tailWord_148496 prefixEnd_148496 76249823270156242417085 := by
  unfold tailWord_148496
  simp only [CollatzResearch.WordTrace]
  refine ⟨2708047035015913971404671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3610729380021218628539561 2708047035015913971404671)
  ·
    refine ⟨4062070552523870957107007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2708047035015913971404671 4062070552523870957107007)
    ·
      refine ⟨6093105828785806435660511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4062070552523870957107007 6093105828785806435660511)
      ·
        refine ⟨9139658743178709653490767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6093105828785806435660511 9139658743178709653490767)
        ·
          refine ⟨13709488114768064480236151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9139658743178709653490767 13709488114768064480236151)
          ·
            refine ⟨20564232172152096720354227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13709488114768064480236151 20564232172152096720354227)
            ·
              refine ⟨30846348258228145080531341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20564232172152096720354227 30846348258228145080531341)
              ·
                refine ⟨11567380596835554405199253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30846348258228145080531341 11567380596835554405199253)
                ·
                  refine ⟨542220965476666612743715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 11567380596835554405199253 542220965476666612743715)
                  ·
                    refine ⟨813331448214999919115573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 542220965476666612743715 813331448214999919115573)
                    ·
                      refine ⟨76249823270156242417085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 813331448214999919115573 76249823270156242417085)
                      ·
                        rfl

theorem cell23_148496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 5].length) (baseStart_148496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_148496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_148496 prefixEnd_148496 := by exact prefixLift 148496
  have htrace : WordTrace (prefixWord ++ tailWord_148496) baseStart_148496 baseEnd_148496 := by
    simpa [prefixWord, tailWord_148496, baseEnd_148496] using wordTrace_append hprefix tailTrace_148496
  have hstable : (prefixWord ++ tailWord_148496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148496).length < 2 ^ (prefixWord ++ tailWord_148496).sum := by decide
  have hdescent : baseEnd_148496 < baseStart_148496 := by decide
  rcases family_descends (prefixWord ++ tailWord_148496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148498 : List Nat := [3, 2, 5, 1, 1, 2, 2, 1, 2, 4]
def baseStart_148498 : Nat := 118140960795 + 148498 * 2 ^ 59
def prefixEnd_148498 : Nat := 4983230072969 + 3 ^ 40 * 148498 * 2
def baseEnd_148498 : Nat := 25416950077155078197359

theorem tailTrace_148498 : CollatzResearch.WordTrace tailWord_148498 prefixEnd_148498 25416950077155078197359 := by
  unfold tailWord_148498
  simp only [CollatzResearch.WordTrace]
  refine ⟨1354041754006145571095537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3610778010683054856254765 1354041754006145571095537)
  ·
    refine ⟨1015531315504609178321653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1354041754006145571095537 1015531315504609178321653)
    ·
      refine ⟨95206060828557110467655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1015531315504609178321653 95206060828557110467655)
      ·
        refine ⟨142809091242835665701483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95206060828557110467655 142809091242835665701483)
        ·
          refine ⟨214213636864253498552225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142809091242835665701483 214213636864253498552225)
          ·
            refine ⟨160660227648190123914169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 214213636864253498552225 160660227648190123914169)
            ·
              refine ⟨120495170736142592935627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160660227648190123914169 120495170736142592935627)
              ·
                refine ⟨180742756104213889403441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120495170736142592935627 180742756104213889403441)
                ·
                  refine ⟨135557067078160417052581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 180742756104213889403441 135557067078160417052581)
                  ·
                    refine ⟨25416950077155078197359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 135557067078160417052581 25416950077155078197359)
                    ·
                      rfl

theorem cell23_148498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_148498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_148498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_148498 prefixEnd_148498 := by exact prefixLift 148498
  have htrace : WordTrace (prefixWord ++ tailWord_148498) baseStart_148498 baseEnd_148498 := by
    simpa [prefixWord, tailWord_148498, baseEnd_148498] using wordTrace_append hprefix tailTrace_148498
  have hstable : (prefixWord ++ tailWord_148498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148498).length < 2 ^ (prefixWord ++ tailWord_148498).sum := by decide
  have hdescent : baseEnd_148498 < baseStart_148498 := by decide
  rcases family_descends (prefixWord ++ tailWord_148498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148504 : List Nat := [2, 1, 2, 3, 2, 4, 2, 1, 2, 1, 3]
def baseStart_148504 : Nat := 118140960795 + 148504 * 2 ^ 59
def prefixEnd_148504 : Nat := 4983230072969 + 3 ^ 40 * 148504 * 2
def baseEnd_148504 : Nat := 76253931115392211117049

theorem tailTrace_148504 : CollatzResearch.WordTrace tailWord_148504 prefixEnd_148504 76253931115392211117049 := by
  unfold tailWord_148504
  simp only [CollatzResearch.WordTrace]
  refine ⟨2708192927001422654550283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3610923902668563539400377 2708192927001422654550283)
  ·
    refine ⟨4062289390502133981825425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2708192927001422654550283 4062289390502133981825425)
    ·
      refine ⟨3046717042876600486369069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4062289390502133981825425 3046717042876600486369069)
      ·
        refine ⟨1142518891078725182388401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3046717042876600486369069 1142518891078725182388401)
        ·
          refine ⟨856889168309043886791301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1142518891078725182388401 856889168309043886791301)
          ·
            refine ⟨160666719057945728773369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 856889168309043886791301 160666719057945728773369)
            ·
              refine ⟨120500039293459296580027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160666719057945728773369 120500039293459296580027)
              ·
                refine ⟨180750058940188944870041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120500039293459296580027 180750058940188944870041)
                ·
                  refine ⟨135562544205141708652531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 180750058940188944870041 135562544205141708652531)
                  ·
                    refine ⟨203343816307712562978797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 135562544205141708652531 203343816307712562978797)
                    ·
                      refine ⟨76253931115392211117049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 203343816307712562978797 76253931115392211117049)
                      ·
                        rfl

theorem cell23_148504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 1, 2, 1, 3].length) (baseStart_148504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_148504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_148504 prefixEnd_148504 := by exact prefixLift 148504
  have htrace : WordTrace (prefixWord ++ tailWord_148504) baseStart_148504 baseEnd_148504 := by
    simpa [prefixWord, tailWord_148504, baseEnd_148504] using wordTrace_append hprefix tailTrace_148504
  have hstable : (prefixWord ++ tailWord_148504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148504).length < 2 ^ (prefixWord ++ tailWord_148504).sum := by decide
  have hdescent : baseEnd_148504 < baseStart_148504 := by decide
  rcases family_descends (prefixWord ++ tailWord_148504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148513 : List Nat := [1, 2, 3, 2, 3, 1, 1, 2, 2, 1, 5]
def baseStart_148513 : Nat := 118140960795 + 148513 * 2 ^ 59
def prefixEnd_148513 : Nat := 4983230072969 + 3 ^ 40 * 148513 * 2
def baseEnd_148513 : Nat := 76258552441282675904507

theorem tailTrace_148513 : CollatzResearch.WordTrace tailWord_148513 prefixEnd_148513 76258552441282675904507 := by
  unfold tailWord_148513
  simp only [CollatzResearch.WordTrace]
  refine ⟨5416714110970239846178193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3611142740646826564118795 5416714110970239846178193)
  ·
    refine ⟨4062535583227679884633645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5416714110970239846178193 4062535583227679884633645)
    ·
      refine ⟨1523450843710379956737617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4062535583227679884633645 1523450843710379956737617)
      ·
        refine ⟨1142588132782784967553213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1523450843710379956737617 1142588132782784967553213)
        ·
          refine ⟨428470549793544362832455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1142588132782784967553213 428470549793544362832455)
          ·
            refine ⟨642705824690316544248683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 428470549793544362832455 642705824690316544248683)
            ·
              refine ⟨964058737035474816373025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 642705824690316544248683 964058737035474816373025)
              ·
                refine ⟨723044052776606112279769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 964058737035474816373025 723044052776606112279769)
                ·
                  refine ⟨542283039582454584209827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 723044052776606112279769 542283039582454584209827)
                  ·
                    refine ⟨813424559373681876314741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 542283039582454584209827 813424559373681876314741)
                    ·
                      refine ⟨76258552441282675904507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 813424559373681876314741 76258552441282675904507)
                      ·
                        rfl

theorem cell23_148513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_148513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_148513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_148513 prefixEnd_148513 := by exact prefixLift 148513
  have htrace : WordTrace (prefixWord ++ tailWord_148513) baseStart_148513 baseEnd_148513 := by
    simpa [prefixWord, tailWord_148513, baseEnd_148513] using wordTrace_append hprefix tailTrace_148513
  have hstable : (prefixWord ++ tailWord_148513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148513).length < 2 ^ (prefixWord ++ tailWord_148513).sum := by decide
  have hdescent : baseEnd_148513 < baseStart_148513 := by decide
  rcases family_descends (prefixWord ++ tailWord_148513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148514 : List Nat := [3, 3, 1, 1, 1, 5, 1, 2, 1, 3, 2]
def baseStart_148514 : Nat := 118140960795 + 148514 * 2 ^ 59
def prefixEnd_148514 : Nat := 4983230072969 + 3 ^ 40 * 148514 * 2
def baseEnd_148514 : Nat := 76259065921937171992003

theorem tailTrace_148514 : CollatzResearch.WordTrace tailWord_148514 prefixEnd_148514 76259065921937171992003 := by
  unfold tailWord_148514
  simp only [CollatzResearch.WordTrace]
  refine ⟨1354187645991654254241149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3611167055977744677976397 1354187645991654254241149)
  ·
    refine ⟨507820367246870345340431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1354187645991654254241149 507820367246870345340431)
    ·
      refine ⟨761730550870305518010647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 507820367246870345340431 761730550870305518010647)
      ·
        refine ⟨1142595826305458277015971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 761730550870305518010647 1142595826305458277015971)
        ·
          refine ⟨1713893739458187415523957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1142595826305458277015971 1713893739458187415523957)
          ·
            refine ⟨160677538074205070205371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1713893739458187415523957 160677538074205070205371)
            ·
              refine ⟨241016307111307605308057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160677538074205070205371 241016307111307605308057)
              ·
                refine ⟨180762230333480703981043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 241016307111307605308057 180762230333480703981043)
                ·
                  refine ⟨271143345500221055971565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 180762230333480703981043 271143345500221055971565)
                  ·
                    refine ⟨101678754562582895989337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 271143345500221055971565 101678754562582895989337)
                    ·
                      refine ⟨76259065921937171992003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 101678754562582895989337 76259065921937171992003)
                      ·
                        rfl

theorem cell23_148514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 2, 1, 3, 2].length) (baseStart_148514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_148514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_148514 prefixEnd_148514 := by exact prefixLift 148514
  have htrace : WordTrace (prefixWord ++ tailWord_148514) baseStart_148514 baseEnd_148514 := by
    simpa [prefixWord, tailWord_148514, baseEnd_148514] using wordTrace_append hprefix tailTrace_148514
  have hstable : (prefixWord ++ tailWord_148514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148514).length < 2 ^ (prefixWord ++ tailWord_148514).sum := by decide
  have hdescent : baseEnd_148514 < baseStart_148514 := by decide
  rcases family_descends (prefixWord ++ tailWord_148514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148543 : List Nat := [1, 1, 2, 2, 3, 1, 1, 4, 2, 3, 3]
def baseStart_148543 : Nat := 118140960795 + 148543 * 2 ^ 59
def prefixEnd_148543 : Nat := 4983230072969 + 3 ^ 40 * 148543 * 2
def baseEnd_148543 : Nat := 76273956860917558529369

theorem tailTrace_148543 : CollatzResearch.WordTrace tailWord_148543 prefixEnd_148543 76273956860917558529369 := by
  unfold tailWord_148543
  simp only [CollatzResearch.WordTrace]
  refine ⟨5417808300861554969770283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3611872200574369979846855 5417808300861554969770283)
  ·
    refine ⟨8126712451292332454655425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5417808300861554969770283 8126712451292332454655425)
    ·
      refine ⟨6095034338469249340991569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8126712451292332454655425 6095034338469249340991569)
      ·
        refine ⟨4571275753851937005743677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6095034338469249340991569 4571275753851937005743677)
        ·
          refine ⟨1714228407694476377153879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4571275753851937005743677 1714228407694476377153879)
          ·
            refine ⟨2571342611541714565730819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1714228407694476377153879 2571342611541714565730819)
            ·
              refine ⟨3857013917312571848596229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2571342611541714565730819 3857013917312571848596229)
              ·
                refine ⟨723190109496107221611793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3857013917312571848596229 723190109496107221611793)
                ·
                  refine ⟨542392582122080416208845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 723190109496107221611793 542392582122080416208845)
                  ·
                    refine ⟨203397218295780156078317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 542392582122080416208845 203397218295780156078317)
                    ·
                      refine ⟨76273956860917558529369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 203397218295780156078317 76273956860917558529369)
                      ·
                        rfl

theorem cell23_148543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 3, 3].length) (baseStart_148543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_148543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_148543 prefixEnd_148543 := by exact prefixLift 148543
  have htrace : WordTrace (prefixWord ++ tailWord_148543) baseStart_148543 baseEnd_148543 := by
    simpa [prefixWord, tailWord_148543, baseEnd_148543] using wordTrace_append hprefix tailTrace_148543
  have hstable : (prefixWord ++ tailWord_148543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148543).length < 2 ^ (prefixWord ++ tailWord_148543).sum := by decide
  have hdescent : baseEnd_148543 < baseStart_148543 := by decide
  rcases family_descends (prefixWord ++ tailWord_148543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148584 : List Nat := [2, 1, 4, 4, 1, 1, 2, 3, 5]
def baseStart_148584 : Nat := 118140960795 + 148584 * 2 ^ 59
def prefixEnd_148584 : Nat := 4983230072969 + 3 ^ 40 * 148584 * 2
def baseEnd_148584 : Nat := 8477223285305766457409

theorem tailTrace_148584 : CollatzResearch.WordTrace tailWord_148584 prefixEnd_148584 8477223285305766457409 := by
  unfold tailWord_148584
  simp only [CollatzResearch.WordTrace]
  refine ⟨2709651846856509486006403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3612869129142012648008537 2709651846856509486006403)
  ·
    refine ⟨4064477770284764229009605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2709651846856509486006403 4064477770284764229009605)
    ·
      refine ⟨762089581928393292939301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4064477770284764229009605 762089581928393292939301)
      ·
        refine ⟨142891796611573742426119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 762089581928393292939301 142891796611573742426119)
        ·
          refine ⟨214337694917360613639179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142891796611573742426119 214337694917360613639179)
          ·
            refine ⟨321506542376040920458769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214337694917360613639179 321506542376040920458769)
            ·
              refine ⟨241129906782030690344077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 321506542376040920458769 241129906782030690344077)
              ·
                refine ⟨90423715043261508879029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 241129906782030690344077 90423715043261508879029)
                ·
                  refine ⟨8477223285305766457409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 90423715043261508879029 8477223285305766457409)
                  ·
                    rfl

theorem cell23_148584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 3, 5].length) (baseStart_148584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_148584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_148584 prefixEnd_148584 := by exact prefixLift 148584
  have htrace : WordTrace (prefixWord ++ tailWord_148584) baseStart_148584 baseEnd_148584 := by
    simpa [prefixWord, tailWord_148584, baseEnd_148584] using wordTrace_append hprefix tailTrace_148584
  have hstable : (prefixWord ++ tailWord_148584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148584).length < 2 ^ (prefixWord ++ tailWord_148584).sum := by decide
  have hdescent : baseEnd_148584 < baseStart_148584 := by decide
  rcases family_descends (prefixWord ++ tailWord_148584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148600 : List Nat := [2, 1, 2, 1, 1, 1, 5, 2, 2, 4, 2]
def baseStart_148600 : Nat := 118140960795 + 148600 * 2 ^ 59
def prefixEnd_148600 : Nat := 4983230072969 + 3 ^ 40 * 148600 * 2
def baseEnd_148600 : Nat := 76303225258223835516607

theorem tailTrace_148600 : CollatzResearch.WordTrace tailWord_148600 prefixEnd_148600 76303225258223835516607 := by
  unfold tailWord_148600
  simp only [CollatzResearch.WordTrace]
  refine ⟨2709943630827526852297627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3613258174436702469730169 2709943630827526852297627)
  ·
    refine ⟨4064915446241290278446441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2709943630827526852297627 4064915446241290278446441)
    ·
      refine ⟨3048686584680967708834831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4064915446241290278446441 3048686584680967708834831)
      ·
        refine ⟨4573029877021451563252247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3048686584680967708834831 4573029877021451563252247)
        ·
          refine ⟨6859544815532177344878371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4573029877021451563252247 6859544815532177344878371)
          ·
            refine ⟨10289317223298266017317557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6859544815532177344878371 10289317223298266017317557)
            ·
              refine ⟨964623489684212439123521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10289317223298266017317557 964623489684212439123521)
              ·
                refine ⟨723467617263159329342641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 964623489684212439123521 723467617263159329342641)
                ·
                  refine ⟨542600712947369497006981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 723467617263159329342641 542600712947369497006981)
                  ·
                    refine ⟨101737633677631780688809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 542600712947369497006981 101737633677631780688809)
                    ·
                      refine ⟨76303225258223835516607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 101737633677631780688809 76303225258223835516607)
                      ·
                        rfl

theorem cell23_148600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 2, 4, 2].length) (baseStart_148600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_148600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_148600 prefixEnd_148600 := by exact prefixLift 148600
  have htrace : WordTrace (prefixWord ++ tailWord_148600) baseStart_148600 baseEnd_148600 := by
    simpa [prefixWord, tailWord_148600, baseEnd_148600] using wordTrace_append hprefix tailTrace_148600
  have hstable : (prefixWord ++ tailWord_148600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148600).length < 2 ^ (prefixWord ++ tailWord_148600).sum := by decide
  have hdescent : baseEnd_148600 < baseStart_148600 := by decide
  rcases family_descends (prefixWord ++ tailWord_148600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148644 : List Nat := [2, 3, 1, 2, 3, 1, 3, 3, 1, 4]
def baseStart_148644 : Nat := 118140960795 + 148644 * 2 ^ 59
def prefixEnd_148644 : Nat := 4983230072969 + 3 ^ 40 * 148644 * 2
def baseEnd_148644 : Nat := 25441939469007221122135

theorem tailTrace_148644 : CollatzResearch.WordTrace tailWord_148644 prefixEnd_148644 25441939469007221122135 := by
  unfold tailWord_148644
  simp only [CollatzResearch.WordTrace]
  refine ⟨2710746036747824609598493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3614328048997099479464657 2710746036747824609598493)
  ·
    refine ⟨1016529763780434228599435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2710746036747824609598493 1016529763780434228599435)
    ·
      refine ⟨1524794645670651342899153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1016529763780434228599435 1524794645670651342899153)
      ·
        refine ⟨1143595984252988507174365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1524794645670651342899153 1143595984252988507174365)
        ·
          refine ⟨428848494094870690190387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1143595984252988507174365 428848494094870690190387)
          ·
            refine ⟨643272741142306035285581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 428848494094870690190387 643272741142306035285581)
            ·
              refine ⟨241227277928364763232093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 643272741142306035285581 241227277928364763232093)
              ·
                refine ⟨90460229223136786212035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 241227277928364763232093 90460229223136786212035)
                ·
                  refine ⟨135690343834705179318053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90460229223136786212035 135690343834705179318053)
                  ·
                    refine ⟨25441939469007221122135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 135690343834705179318053 25441939469007221122135)
                    ·
                      rfl

theorem cell23_148644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 3, 1, 4].length) (baseStart_148644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_148644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_148644 prefixEnd_148644 := by exact prefixLift 148644
  have htrace : WordTrace (prefixWord ++ tailWord_148644) baseStart_148644 baseEnd_148644 := by
    simpa [prefixWord, tailWord_148644, baseEnd_148644] using wordTrace_append hprefix tailTrace_148644
  have hstable : (prefixWord ++ tailWord_148644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148644).length < 2 ^ (prefixWord ++ tailWord_148644).sum := by decide
  have hdescent : baseEnd_148644 < baseStart_148644 := by decide
  rcases family_descends (prefixWord ++ tailWord_148644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148734 : List Nat := [4, 2, 2, 1, 1, 2, 2, 3, 2, 4]
def baseStart_148734 : Nat := 118140960795 + 148734 * 2 ^ 59
def prefixEnd_148734 : Nat := 4983230072969 + 3 ^ 40 * 148734 * 2
def baseEnd_148734 : Nat := 25457343888642103746997

theorem tailTrace_148734 : CollatzResearch.WordTrace tailWord_148734 prefixEnd_148734 25457343888642103746997 := by
  unfold tailWord_148734
  simp only [CollatzResearch.WordTrace]
  refine ⟨678096830396199323746657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3616516428779729726648837 678096830396199323746657)
  ·
    refine ⟨508572622797149492809993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 678096830396199323746657 508572622797149492809993)
    ·
      refine ⟨381429467097862119607495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 508572622797149492809993 381429467097862119607495)
      ·
        refine ⟨572144200646793179411243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 381429467097862119607495 572144200646793179411243)
        ·
          refine ⟨858216300970189769116865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 572144200646793179411243 858216300970189769116865)
          ·
            refine ⟨643662225727642326837649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 858216300970189769116865 643662225727642326837649)
            ·
              refine ⟨482746669295731745128237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 643662225727642326837649 482746669295731745128237)
              ·
                refine ⟨181030000985899404423089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 482746669295731745128237 181030000985899404423089)
                ·
                  refine ⟨135772500739424553317317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 181030000985899404423089 135772500739424553317317)
                  ·
                    refine ⟨25457343888642103746997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 135772500739424553317317 25457343888642103746997)
                    ·
                      rfl

theorem cell23_148734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_148734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_148734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_148734 prefixEnd_148734 := by exact prefixLift 148734
  have htrace : WordTrace (prefixWord ++ tailWord_148734) baseStart_148734 baseEnd_148734 := by
    simpa [prefixWord, tailWord_148734, baseEnd_148734] using wordTrace_append hprefix tailTrace_148734
  have hstable : (prefixWord ++ tailWord_148734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148734).length < 2 ^ (prefixWord ++ tailWord_148734).sum := by decide
  have hdescent : baseEnd_148734 < baseStart_148734 := by decide
  rcases family_descends (prefixWord ++ tailWord_148734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148737 : List Nat := [1, 2, 4, 1, 1, 4, 2, 1, 1, 2, 4]
def baseStart_148737 : Nat := 118140960795 + 148737 * 2 ^ 59
def prefixEnd_148737 : Nat := 4983230072969 + 3 ^ 40 * 148737 * 2
def baseEnd_148737 : Nat := 76373572107889799503477

theorem tailTrace_148737 : CollatzResearch.WordTrace tailWord_148737 prefixEnd_148737 76373572107889799503477 := by
  unfold tailWord_148737
  simp only [CollatzResearch.WordTrace]
  refine ⟨5424884062158726102332465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3616589374772484068221643 5424884062158726102332465)
  ·
    refine ⟨4068663046619044576749349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5424884062158726102332465 4068663046619044576749349)
    ·
      refine ⟨762874321241070858140503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4068663046619044576749349 762874321241070858140503)
      ·
        refine ⟨1144311481861606287210755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 762874321241070858140503 1144311481861606287210755)
        ·
          refine ⟨1716467222792409430816133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1144311481861606287210755 1716467222792409430816133)
          ·
            refine ⟨321837604273576768278025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1716467222792409430816133 321837604273576768278025)
            ·
              refine ⟨241378203205182576208519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 321837604273576768278025 241378203205182576208519)
              ·
                refine ⟨362067304807773864312779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 241378203205182576208519 362067304807773864312779)
                ·
                  refine ⟨543100957211660796469169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 362067304807773864312779 543100957211660796469169)
                  ·
                    refine ⟨407325717908745597351877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 543100957211660796469169 407325717908745597351877)
                    ·
                      refine ⟨76373572107889799503477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 407325717908745597351877 76373572107889799503477)
                      ·
                        rfl

theorem cell23_148737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_148737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_148737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_148737 prefixEnd_148737 := by exact prefixLift 148737
  have htrace : WordTrace (prefixWord ++ tailWord_148737) baseStart_148737 baseEnd_148737 := by
    simpa [prefixWord, tailWord_148737, baseEnd_148737] using wordTrace_append hprefix tailTrace_148737
  have hstable : (prefixWord ++ tailWord_148737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148737).length < 2 ^ (prefixWord ++ tailWord_148737).sum := by decide
  have hdescent : baseEnd_148737 < baseStart_148737 := by decide
  rcases family_descends (prefixWord ++ tailWord_148737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148757 : List Nat := [1, 3, 2, 1, 2, 1, 1, 4, 4, 1, 3]
def baseStart_148757 : Nat := 118140960795 + 148757 * 2 ^ 59
def prefixEnd_148757 : Nat := 4983230072969 + 3 ^ 40 * 148757 * 2
def baseEnd_148757 : Nat := 76383841720979721253385

theorem tailTrace_148757 : CollatzResearch.WordTrace tailWord_148757 prefixEnd_148757 76383841720979721253385 := by
  unfold tailWord_148757
  simp only [CollatzResearch.WordTrace]
  refine ⟨5425613522086269518060525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3617075681390846345373683 5425613522086269518060525)
  ·
    refine ⟨2034605070782351069272697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5425613522086269518060525 2034605070782351069272697)
    ·
      refine ⟨1525953803086763301954523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2034605070782351069272697 1525953803086763301954523)
      ·
        refine ⟨2288930704630144952931785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1525953803086763301954523 2288930704630144952931785)
        ·
          refine ⟨1716698028472608714698839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2288930704630144952931785 1716698028472608714698839)
          ·
            refine ⟨2575047042708913072048259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1716698028472608714698839 2575047042708913072048259)
            ·
              refine ⟨3862570564063369608072389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2575047042708913072048259 3862570564063369608072389)
              ·
                refine ⟨724231980761881801513573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3862570564063369608072389 724231980761881801513573)
                ·
                  refine ⟨135793496392852837783795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 724231980761881801513573 135793496392852837783795)
                  ·
                    refine ⟨203690244589279256675693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 135793496392852837783795 203690244589279256675693)
                    ·
                      refine ⟨76383841720979721253385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 203690244589279256675693 76383841720979721253385)
                      ·
                        rfl

theorem cell23_148757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 4, 1, 3].length) (baseStart_148757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_148757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_148757 prefixEnd_148757 := by exact prefixLift 148757
  have htrace : WordTrace (prefixWord ++ tailWord_148757) baseStart_148757 baseEnd_148757 := by
    simpa [prefixWord, tailWord_148757, baseEnd_148757] using wordTrace_append hprefix tailTrace_148757
  have hstable : (prefixWord ++ tailWord_148757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148757).length < 2 ^ (prefixWord ++ tailWord_148757).sum := by decide
  have hdescent : baseEnd_148757 < baseStart_148757 := by decide
  rcases family_descends (prefixWord ++ tailWord_148757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148800 : List Nat := [2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 5]
def baseStart_148800 : Nat := 118140960795 + 148800 * 2 ^ 59
def prefixEnd_148800 : Nat := 4983230072969 + 3 ^ 40 * 148800 * 2
def baseEnd_148800 : Nat := 76405921389123053015687

theorem tailTrace_148800 : CollatzResearch.WordTrace tailWord_148800 prefixEnd_148800 76405921389123053015687 := by
  unfold tailWord_148800
  simp only [CollatzResearch.WordTrace]
  refine ⟨2713590930465243930937927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3618121240620325241250569 2713590930465243930937927)
  ·
    refine ⟨4070386395697865896406891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2713590930465243930937927 4070386395697865896406891)
    ·
      refine ⟨6105579593546798844610337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4070386395697865896406891 6105579593546798844610337)
      ·
        refine ⟨4579184695160099133457753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6105579593546798844610337 4579184695160099133457753)
        ·
          refine ⟨3434388521370074350093315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4579184695160099133457753 3434388521370074350093315)
          ·
            refine ⟨5151582782055111525139973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3434388521370074350093315 5151582782055111525139973)
            ·
              refine ⟨965921771635333410963745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5151582782055111525139973 965921771635333410963745)
              ·
                refine ⟨724441328726500058222809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 965921771635333410963745 724441328726500058222809)
                ·
                  refine ⟨543330996544875043667107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 724441328726500058222809 543330996544875043667107)
                  ·
                    refine ⟨814996494817312565500661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 543330996544875043667107 814996494817312565500661)
                    ·
                      refine ⟨76405921389123053015687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 814996494817312565500661 76405921389123053015687)
                      ·
                        rfl

theorem cell23_148800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 5].length) (baseStart_148800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_148800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_148800 prefixEnd_148800 := by exact prefixLift 148800
  have htrace : WordTrace (prefixWord ++ tailWord_148800) baseStart_148800 baseEnd_148800 := by
    simpa [prefixWord, tailWord_148800, baseEnd_148800] using wordTrace_append hprefix tailTrace_148800
  have hstable : (prefixWord ++ tailWord_148800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148800).length < 2 ^ (prefixWord ++ tailWord_148800).sum := by decide
  have hdescent : baseEnd_148800 < baseStart_148800 := by decide
  rcases family_descends (prefixWord ++ tailWord_148800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148801 : List Nat := [1, 2, 5, 2, 1, 1, 1, 4, 1, 3, 2]
def baseStart_148801 : Nat := 118140960795 + 148801 * 2 ^ 59
def prefixEnd_148801 : Nat := 4983230072969 + 3 ^ 40 * 148801 * 2
def baseEnd_148801 : Nat := 76406434869777549103183

theorem tailTrace_148801 : CollatzResearch.WordTrace tailWord_148801 prefixEnd_148801 76406434869777549103183 := by
  unfold tailWord_148801
  simp only [CollatzResearch.WordTrace]
  refine ⟨5427218333926865032662257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3618145555951243355108171 5427218333926865032662257)
  ·
    refine ⟨4070413750445148774496693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5427218333926865032662257 4070413750445148774496693)
    ·
      refine ⟨381601289104232697609065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4070413750445148774496693 381601289104232697609065)
      ·
        refine ⟨286200966828174523206799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 381601289104232697609065 286200966828174523206799)
        ·
          refine ⟨429301450242261784810199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286200966828174523206799 429301450242261784810199)
          ·
            refine ⟨643952175363392677215299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 429301450242261784810199 643952175363392677215299)
            ·
              refine ⟨965928263045089015822949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 643952175363392677215299 965928263045089015822949)
              ·
                refine ⟨181111549320954190466803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 965928263045089015822949 181111549320954190466803)
                ·
                  refine ⟨271667323981431285700205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 181111549320954190466803 271667323981431285700205)
                  ·
                    refine ⟨101875246493036732137577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 271667323981431285700205 101875246493036732137577)
                    ·
                      refine ⟨76406434869777549103183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 101875246493036732137577 76406434869777549103183)
                      ·
                        rfl

theorem cell23_148801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_148801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_148801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_148801 prefixEnd_148801 := by exact prefixLift 148801
  have htrace : WordTrace (prefixWord ++ tailWord_148801) baseStart_148801 baseEnd_148801 := by
    simpa [prefixWord, tailWord_148801, baseEnd_148801] using wordTrace_append hprefix tailTrace_148801
  have hstable : (prefixWord ++ tailWord_148801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148801).length < 2 ^ (prefixWord ++ tailWord_148801).sum := by decide
  have hdescent : baseEnd_148801 < baseStart_148801 := by decide
  rcases family_descends (prefixWord ++ tailWord_148801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148810 : List Nat := [3, 1, 2, 1, 1, 1, 1, 4, 1, 4, 4]
def baseStart_148810 : Nat := 118140960795 + 148810 * 2 ^ 59
def prefixEnd_148810 : Nat := 4983230072969 + 3 ^ 40 * 148810 * 2
def baseEnd_148810 : Nat := 76411056195668013890641

theorem tailTrace_148810 : CollatzResearch.WordTrace tailWord_148810 prefixEnd_148810 76411056195668013890641 := by
  unfold tailWord_148810
  simp only [CollatzResearch.WordTrace]
  refine ⟨1356886647723564892434971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3618364393929506379826589 1356886647723564892434971)
  ·
    refine ⟨2035329971585347338652457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1356886647723564892434971 2035329971585347338652457)
    ·
      refine ⟨1526497478689010503989343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2035329971585347338652457 1526497478689010503989343)
      ·
        refine ⟨2289746218033515755984015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1526497478689010503989343 2289746218033515755984015)
        ·
          refine ⟨3434619327050273633976023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2289746218033515755984015 3434619327050273633976023)
          ·
            refine ⟨5151928990575410450964035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3434619327050273633976023 5151928990575410450964035)
            ·
              refine ⟨7727893485863115676446053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5151928990575410450964035 7727893485863115676446053)
              ·
                refine ⟨1448980028599334189333635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7727893485863115676446053 1448980028599334189333635)
                ·
                  refine ⟨2173470042899001284000453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1448980028599334189333635 2173470042899001284000453)
                  ·
                    refine ⟨407525633043562740750085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2173470042899001284000453 407525633043562740750085)
                    ·
                      refine ⟨76411056195668013890641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 407525633043562740750085 76411056195668013890641)
                      ·
                        rfl

theorem cell23_148810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_148810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_148810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_148810 prefixEnd_148810 := by exact prefixLift 148810
  have htrace : WordTrace (prefixWord ++ tailWord_148810) baseStart_148810 baseEnd_148810 := by
    simpa [prefixWord, tailWord_148810, baseEnd_148810] using wordTrace_append hprefix tailTrace_148810
  have hstable : (prefixWord ++ tailWord_148810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148810).length < 2 ^ (prefixWord ++ tailWord_148810).sum := by decide
  have hdescent : baseEnd_148810 < baseStart_148810 := by decide
  rcases family_descends (prefixWord ++ tailWord_148810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148814 : List Nat := [4, 1, 1, 1, 1, 1, 3, 1, 6, 2, 2]
def baseStart_148814 : Nat := 118140960795 + 148814 * 2 ^ 59
def prefixEnd_148814 : Nat := 4983230072969 + 3 ^ 40 * 148814 * 2
def baseEnd_148814 : Nat := 76413110118285998240623

theorem tailTrace_148814 : CollatzResearch.WordTrace tailWord_148814 prefixEnd_148814 76413110118285998240623 := by
  unfold tailWord_148814
  simp only [CollatzResearch.WordTrace]
  refine ⟨678461560359971031610687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3618461655253178835256997 678461560359971031610687)
  ·
    refine ⟨1017692340539956547416031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 678461560359971031610687 1017692340539956547416031)
    ·
      refine ⟨1526538510809934821124047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1017692340539956547416031 1526538510809934821124047)
      ·
        refine ⟨2289807766214902231686071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1526538510809934821124047 2289807766214902231686071)
        ·
          refine ⟨3434711649322353347529107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2289807766214902231686071 3434711649322353347529107)
          ·
            refine ⟨5152067473983530021293661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3434711649322353347529107 5152067473983530021293661)
            ·
              refine ⟨1932025302743823757985123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5152067473983530021293661 1932025302743823757985123)
              ·
                refine ⟨2898037954115735636977685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1932025302743823757985123 2898037954115735636977685)
                ·
                  refine ⟨135845529099175107983329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2898037954115735636977685 135845529099175107983329)
                  ·
                    refine ⟨101884146824381330987497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 135845529099175107983329 101884146824381330987497)
                    ·
                      refine ⟨76413110118285998240623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 101884146824381330987497 76413110118285998240623)
                      ·
                        rfl

theorem cell23_148814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 6, 2, 2].length) (baseStart_148814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_148814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_148814 prefixEnd_148814 := by exact prefixLift 148814
  have htrace : WordTrace (prefixWord ++ tailWord_148814) baseStart_148814 baseEnd_148814 := by
    simpa [prefixWord, tailWord_148814, baseEnd_148814] using wordTrace_append hprefix tailTrace_148814
  have hstable : (prefixWord ++ tailWord_148814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148814).length < 2 ^ (prefixWord ++ tailWord_148814).sum := by decide
  have hdescent : baseEnd_148814 < baseStart_148814 := by decide
  rcases family_descends (prefixWord ++ tailWord_148814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148860 : List Nat := [2, 2, 2, 1, 1, 1, 3, 2, 1, 1, 7]
def baseStart_148860 : Nat := 118140960795 + 148860 * 2 ^ 59
def prefixEnd_148860 : Nat := 4983230072969 + 3 ^ 40 * 148860 * 2
def baseEnd_148860 : Nat := 76436730228392818265411

theorem tailTrace_148860 : CollatzResearch.WordTrace tailWord_148860 prefixEnd_148860 76436730228392818265411 := by
  unfold tailWord_148860
  simp only [CollatzResearch.WordTrace]
  refine ⟨2714685120356559054530017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3619580160475412072706689 2714685120356559054530017)
  ·
    refine ⟨2036013840267419290897513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2714685120356559054530017 2036013840267419290897513)
    ·
      refine ⟨1527010380200564468173135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2036013840267419290897513 1527010380200564468173135)
      ·
        refine ⟨2290515570300846702259703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1527010380200564468173135 2290515570300846702259703)
        ·
          refine ⟨3435773355451270053389555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2290515570300846702259703 3435773355451270053389555)
          ·
            refine ⟨5153660033176905080084333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3435773355451270053389555 5153660033176905080084333)
            ·
              refine ⟨1932622512441339405031625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5153660033176905080084333 1932622512441339405031625)
              ·
                refine ⟨1449466884331004553773719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1932622512441339405031625 1449466884331004553773719)
                ·
                  refine ⟨2174200326496506830660579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1449466884331004553773719 2174200326496506830660579)
                  ·
                    refine ⟨3261300489744760245990869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2174200326496506830660579 3261300489744760245990869)
                    ·
                      refine ⟨76436730228392818265411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 3261300489744760245990869 76436730228392818265411)
                      ·
                        rfl

theorem cell23_148860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_148860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_148860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_148860 prefixEnd_148860 := by exact prefixLift 148860
  have htrace : WordTrace (prefixWord ++ tailWord_148860) baseStart_148860 baseEnd_148860 := by
    simpa [prefixWord, tailWord_148860, baseEnd_148860] using wordTrace_append hprefix tailTrace_148860
  have hstable : (prefixWord ++ tailWord_148860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148860).length < 2 ^ (prefixWord ++ tailWord_148860).sum := by decide
  have hdescent : baseEnd_148860 < baseStart_148860 := by decide
  rcases family_descends (prefixWord ++ tailWord_148860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148867 : List Nat := [1, 1, 1, 3, 5, 1, 1, 3, 2, 5]
def baseStart_148867 : Nat := 118140960795 + 148867 * 2 ^ 59
def prefixEnd_148867 : Nat := 4983230072969 + 3 ^ 40 * 148867 * 2
def baseEnd_148867 : Nat := 25480108197658096959293

theorem tailTrace_148867 : CollatzResearch.WordTrace tailWord_148867 prefixEnd_148867 25480108197658096959293 := by
  unfold tailWord_148867
  simp only [CollatzResearch.WordTrace]
  refine ⟨5429625551687758304564855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3619750367791838869709903 5429625551687758304564855)
  ·
    refine ⟨8144438327531637456847283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5429625551687758304564855 8144438327531637456847283)
    ·
      refine ⟨12216657491297456185270925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8144438327531637456847283 12216657491297456185270925)
      ·
        refine ⟨4581246559236546069476597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12216657491297456185270925 4581246559236546069476597)
        ·
          refine ⟨429491864928426194013431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4581246559236546069476597 429491864928426194013431)
          ·
            refine ⟨644237797392639291020147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 429491864928426194013431 644237797392639291020147)
            ·
              refine ⟨966356696088958936530221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 644237797392639291020147 966356696088958936530221)
              ·
                refine ⟨362383761033359601198833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 966356696088958936530221 362383761033359601198833)
                ·
                  refine ⟨271787820775019700899125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 362383761033359601198833 271787820775019700899125)
                  ·
                    refine ⟨25480108197658096959293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 271787820775019700899125 25480108197658096959293)
                    ·
                      rfl

theorem cell23_148867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 2, 5].length) (baseStart_148867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_148867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_148867 prefixEnd_148867 := by exact prefixLift 148867
  have htrace : WordTrace (prefixWord ++ tailWord_148867) baseStart_148867 baseEnd_148867 := by
    simpa [prefixWord, tailWord_148867, baseEnd_148867] using wordTrace_append hprefix tailTrace_148867
  have hstable : (prefixWord ++ tailWord_148867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148867).length < 2 ^ (prefixWord ++ tailWord_148867).sum := by decide
  have hdescent : baseEnd_148867 < baseStart_148867 := by decide
  rcases family_descends (prefixWord ++ tailWord_148867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148884 : List Nat := [2, 4, 2, 1, 2, 1, 2, 2, 2, 5]
def baseStart_148884 : Nat := 118140960795 + 148884 * 2 ^ 59
def prefixEnd_148884 : Nat := 4983230072969 + 3 ^ 40 * 148884 * 2
def baseEnd_148884 : Nat := 25483017921366908121767

theorem tailTrace_148884 : CollatzResearch.WordTrace tailWord_148884 prefixEnd_148884 25483017921366908121767 := by
  unfold tailWord_148884
  simp only [CollatzResearch.WordTrace]
  refine ⟨2715122796313085103966853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3620163728417446805289137 2715122796313085103966853)
  ·
    refine ⟨509085524308703456993785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2715122796313085103966853 509085524308703456993785)
    ·
      refine ⟨381814143231527592745339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 509085524308703456993785 381814143231527592745339)
      ·
        refine ⟨572721214847291389118009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 381814143231527592745339 572721214847291389118009)
        ·
          refine ⟨429540911135468541838507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 572721214847291389118009 429540911135468541838507)
          ·
            refine ⟨644311366703202812757761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 429540911135468541838507 644311366703202812757761)
            ·
              refine ⟨483233525027402109568321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 644311366703202812757761 483233525027402109568321)
              ·
                refine ⟨362425143770551582176241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 483233525027402109568321 362425143770551582176241)
                ·
                  refine ⟨271818857827913686632181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 362425143770551582176241 271818857827913686632181)
                  ·
                    refine ⟨25483017921366908121767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 271818857827913686632181 25483017921366908121767)
                    ·
                      rfl

theorem cell23_148884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_148884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_148884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_148884 prefixEnd_148884 := by exact prefixLift 148884
  have htrace : WordTrace (prefixWord ++ tailWord_148884) baseStart_148884 baseEnd_148884 := by
    simpa [prefixWord, tailWord_148884, baseEnd_148884] using wordTrace_append hprefix tailTrace_148884
  have hstable : (prefixWord ++ tailWord_148884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148884).length < 2 ^ (prefixWord ++ tailWord_148884).sum := by decide
  have hdescent : baseEnd_148884 < baseStart_148884 := by decide
  rcases family_descends (prefixWord ++ tailWord_148884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148888 : List Nat := [2, 1, 2, 5, 2, 2, 2, 2, 5]
def baseStart_148888 : Nat := 118140960795 + 148888 * 2 ^ 59
def prefixEnd_148888 : Nat := 4983230072969 + 3 ^ 40 * 148888 * 2
def baseEnd_148888 : Nat := 8494567520746523190587

theorem tailTrace_148888 : CollatzResearch.WordTrace tailWord_148888 prefixEnd_148888 8494567520746523190587 := by
  unfold tailWord_148888
  simp only [CollatzResearch.WordTrace]
  refine ⟨2715195742305839445539659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3620260989741119260719545 2715195742305839445539659)
  ·
    refine ⟨4072793613458759168309489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2715195742305839445539659 4072793613458759168309489)
    ·
      refine ⟨3054595210094069376232117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4072793613458759168309489 3054595210094069376232117)
      ·
        refine ⟨286368300946319004021761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3054595210094069376232117 286368300946319004021761)
        ·
          refine ⟨214776225709739253016321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 286368300946319004021761 214776225709739253016321)
          ·
            refine ⟨161082169282304439762241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 214776225709739253016321 161082169282304439762241)
            ·
              refine ⟨120811626961728329821681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161082169282304439762241 120811626961728329821681)
              ·
                refine ⟨90608720221296247366261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120811626961728329821681 90608720221296247366261)
                ·
                  refine ⟨8494567520746523190587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 90608720221296247366261 8494567520746523190587)
                  ·
                    rfl

theorem cell23_148888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 2, 5].length) (baseStart_148888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_148888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_148888 prefixEnd_148888 := by exact prefixLift 148888
  have htrace : WordTrace (prefixWord ++ tailWord_148888) baseStart_148888 baseEnd_148888 := by
    simpa [prefixWord, tailWord_148888, baseEnd_148888] using wordTrace_append hprefix tailTrace_148888
  have hstable : (prefixWord ++ tailWord_148888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148888).length < 2 ^ (prefixWord ++ tailWord_148888).sum := by decide
  have hdescent : baseEnd_148888 < baseStart_148888 := by decide
  rcases family_descends (prefixWord ++ tailWord_148888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148921 : List Nat := [1, 2, 1, 4, 4, 2, 1, 1, 2, 1, 4]
def baseStart_148921 : Nat := 118140960795 + 148921 * 2 ^ 59
def prefixEnd_148921 : Nat := 4983230072969 + 3 ^ 40 * 148921 * 2
def baseEnd_148921 : Nat := 76468052548317079602631

theorem tailTrace_148921 : CollatzResearch.WordTrace tailWord_148921 prefixEnd_148921 76468052548317079602631 := by
  unfold tailWord_148921
  simp only [CollatzResearch.WordTrace]
  refine ⟨5431595093492125527030617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3621063395661417018020411 5431595093492125527030617)
  ·
    refine ⟨4073696320119094145272963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5431595093492125527030617 4073696320119094145272963)
    ·
      refine ⟨6110544480178641217909445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4073696320119094145272963 6110544480178641217909445)
      ·
        refine ⟨1145727090033495228358021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6110544480178641217909445 1145727090033495228358021)
        ·
          refine ⟨214823829381280355317129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1145727090033495228358021 214823829381280355317129)
          ·
            refine ⟨161117872035960266487847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 214823829381280355317129 161117872035960266487847)
            ·
              refine ⟨241676808053940399731771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161117872035960266487847 241676808053940399731771)
              ·
                refine ⟨362515212080910599597657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 241676808053940399731771 362515212080910599597657)
                ·
                  refine ⟨271886409060682949698243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 362515212080910599597657 271886409060682949698243)
                  ·
                    refine ⟨407829613591024424547365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 271886409060682949698243 407829613591024424547365)
                    ·
                      refine ⟨76468052548317079602631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 407829613591024424547365 76468052548317079602631)
                      ·
                        rfl

theorem cell23_148921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_148921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_148921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_148921 prefixEnd_148921 := by exact prefixLift 148921
  have htrace : WordTrace (prefixWord ++ tailWord_148921) baseStart_148921 baseEnd_148921 := by
    simpa [prefixWord, tailWord_148921, baseEnd_148921] using wordTrace_append hprefix tailTrace_148921
  have hstable : (prefixWord ++ tailWord_148921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148921).length < 2 ^ (prefixWord ++ tailWord_148921).sum := by decide
  have hdescent : baseEnd_148921 < baseStart_148921 := by decide
  rcases family_descends (prefixWord ++ tailWord_148921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148988 : List Nat := [2, 2, 2, 1, 2, 1, 5, 3, 1, 1, 3]
def baseStart_148988 : Nat := 118140960795 + 148988 * 2 ^ 59
def prefixEnd_148988 : Nat := 4983230072969 + 3 ^ 40 * 148988 * 2
def baseEnd_148988 : Nat := 76502455752168317464823

theorem tailTrace_148988 : CollatzResearch.WordTrace tailWord_148988 prefixEnd_148988 76502455752168317464823 := by
  unfold tailWord_148988
  simp only [CollatzResearch.WordTrace]
  refine ⟨2717019392124697984859809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3622692522832930646479745 2717019392124697984859809)
  ·
    refine ⟨2037764544093523488644857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2717019392124697984859809 2037764544093523488644857)
    ·
      refine ⟨1528323408070142616483643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2037764544093523488644857 1528323408070142616483643)
      ·
        refine ⟨2292485112105213924725465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1528323408070142616483643 2292485112105213924725465)
        ·
          refine ⟨1719363834078910443544099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2292485112105213924725465 1719363834078910443544099)
          ·
            refine ⟨2579045751118365665316149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1719363834078910443544099 2579045751118365665316149)
            ·
              refine ⟨241785539167346781123389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2579045751118365665316149 241785539167346781123389)
              ·
                refine ⟨90669577187755042921271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 241785539167346781123389 90669577187755042921271)
                ·
                  refine ⟨136004365781632564381907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90669577187755042921271 136004365781632564381907)
                  ·
                    refine ⟨204006548672448846572861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 136004365781632564381907 204006548672448846572861)
                    ·
                      refine ⟨76502455752168317464823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 204006548672448846572861 76502455752168317464823)
                      ·
                        rfl

theorem cell23_148988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 3, 1, 1, 3].length) (baseStart_148988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_148988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_148988 prefixEnd_148988 := by exact prefixLift 148988
  have htrace : WordTrace (prefixWord ++ tailWord_148988) baseStart_148988 baseEnd_148988 := by
    simpa [prefixWord, tailWord_148988, baseEnd_148988] using wordTrace_append hprefix tailTrace_148988
  have hstable : (prefixWord ++ tailWord_148988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148988).length < 2 ^ (prefixWord ++ tailWord_148988).sum := by decide
  have hdescent : baseEnd_148988 < baseStart_148988 := by decide
  rcases family_descends (prefixWord ++ tailWord_148988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149021 : List Nat := [1, 4, 2, 2, 1, 1, 3, 3, 2, 4]
def baseStart_149021 : Nat := 118140960795 + 149021 * 2 ^ 59
def prefixEnd_149021 : Nat := 4983230072969 + 3 ^ 40 * 149021 * 2
def baseEnd_149021 : Nat := 25506466871255562784057

theorem tailTrace_149021 : CollatzResearch.WordTrace tailWord_149021 prefixEnd_149021 25506466871255562784057 := by
  unfold tailWord_149021
  simp only [CollatzResearch.WordTrace]
  refine ⟨5435242393129842605670917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3623494928753228403780611 5435242393129842605670917)
  ·
    refine ⟨1019107948711845488563297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5435242393129842605670917 1019107948711845488563297)
    ·
      refine ⟨764330961533884116422473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1019107948711845488563297 764330961533884116422473)
      ·
        refine ⟨573248221150413087316855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 764330961533884116422473 573248221150413087316855)
        ·
          refine ⟨859872331725619630975283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 573248221150413087316855 859872331725619630975283)
          ·
            refine ⟨1289808497588429446462925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 859872331725619630975283 1289808497588429446462925)
            ·
              refine ⟨483678186595661042423597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1289808497588429446462925 483678186595661042423597)
              ·
                refine ⟨181379319973372890908849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 483678186595661042423597 181379319973372890908849)
                ·
                  refine ⟨136034489980029668181637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 181379319973372890908849 136034489980029668181637)
                  ·
                    refine ⟨25506466871255562784057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 136034489980029668181637 25506466871255562784057)
                    ·
                      rfl

theorem cell23_149021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_149021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_149021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_149021 prefixEnd_149021 := by exact prefixLift 149021
  have htrace : WordTrace (prefixWord ++ tailWord_149021) baseStart_149021 baseEnd_149021 := by
    simpa [prefixWord, tailWord_149021, baseEnd_149021] using wordTrace_append hprefix tailTrace_149021
  have hstable : (prefixWord ++ tailWord_149021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149021).length < 2 ^ (prefixWord ++ tailWord_149021).sum := by decide
  have hdescent : baseEnd_149021 < baseStart_149021 := by decide
  rcases family_descends (prefixWord ++ tailWord_149021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149024 : List Nat := [2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 6]
def baseStart_149024 : Nat := 118140960795 + 149024 * 2 ^ 59
def prefixEnd_149024 : Nat := 4983230072969 + 3 ^ 40 * 149024 * 2
def baseEnd_149024 : Nat := 76520941055730176614657

theorem tailTrace_149024 : CollatzResearch.WordTrace tailWord_149024 prefixEnd_149024 76520941055730176614657 := by
  unfold tailWord_149024
  simp only [CollatzResearch.WordTrace]
  refine ⟨2717675906059487059015063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3623567874745982745353417 2717675906059487059015063)
  ·
    refine ⟨4076513859089230588522595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2717675906059487059015063 4076513859089230588522595)
    ·
      refine ⟨6114770788633845882783893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4076513859089230588522595 6114770788633845882783893)
      ·
        refine ⟨286629880717211525755495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6114770788633845882783893 286629880717211525755495)
        ·
          refine ⟨429944821075817288633243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286629880717211525755495 429944821075817288633243)
          ·
            refine ⟨644917231613725932949865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 429944821075817288633243 644917231613725932949865)
            ·
              refine ⟨483687923710294449712399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 644917231613725932949865 483687923710294449712399)
              ·
                refine ⟨725531885565441674568599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 483687923710294449712399 725531885565441674568599)
                ·
                  refine ⟨1088297828348162511852899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 725531885565441674568599 1088297828348162511852899)
                  ·
                    refine ⟨1632446742522243767779349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1088297828348162511852899 1632446742522243767779349)
                    ·
                      refine ⟨76520941055730176614657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1632446742522243767779349 76520941055730176614657)
                      ·
                        rfl

theorem cell23_149024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_149024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_149024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_149024 prefixEnd_149024 := by exact prefixLift 149024
  have htrace : WordTrace (prefixWord ++ tailWord_149024) baseStart_149024 baseEnd_149024 := by
    simpa [prefixWord, tailWord_149024, baseEnd_149024] using wordTrace_append hprefix tailTrace_149024
  have hstable : (prefixWord ++ tailWord_149024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149024).length < 2 ^ (prefixWord ++ tailWord_149024).sum := by decide
  have hdescent : baseEnd_149024 < baseStart_149024 := by decide
  rcases family_descends (prefixWord ++ tailWord_149024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149048 : List Nat := [2, 1, 2, 1, 4, 3, 3, 1, 1, 2, 3]
def baseStart_149048 : Nat := 118140960795 + 149048 * 2 ^ 59
def prefixEnd_149048 : Nat := 4983230072969 + 3 ^ 40 * 149048 * 2
def baseEnd_149048 : Nat := 76533264591438082714547

theorem tailTrace_149048 : CollatzResearch.WordTrace tailWord_149048 prefixEnd_149048 76533264591438082714547 := by
  unfold tailWord_149048
  simp only [CollatzResearch.WordTrace]
  refine ⟨2718113582016013108451899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3624151442688017477935865 2718113582016013108451899)
  ·
    refine ⟨4077170373024019662677849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2718113582016013108451899 4077170373024019662677849)
    ·
      refine ⟨3057877779768014747008387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4077170373024019662677849 3057877779768014747008387)
      ·
        refine ⟨4586816669652022120512581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3057877779768014747008387 4586816669652022120512581)
        ·
          refine ⟨860028125559754147596109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4586816669652022120512581 860028125559754147596109)
          ·
            refine ⟨322510547084907805348541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 860028125559754147596109 322510547084907805348541)
            ·
              refine ⟨120941455156840427005703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 322510547084907805348541 120941455156840427005703)
              ·
                refine ⟨181412182735260640508555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120941455156840427005703 181412182735260640508555)
                ·
                  refine ⟨272118274102890960762833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 181412182735260640508555 272118274102890960762833)
                  ·
                    refine ⟨204088705577168220572125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 272118274102890960762833 204088705577168220572125)
                    ·
                      refine ⟨76533264591438082714547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 204088705577168220572125 76533264591438082714547)
                      ·
                        rfl

theorem cell23_149048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 1, 1, 2, 3].length) (baseStart_149048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_149048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_149048 prefixEnd_149048 := by exact prefixLift 149048
  have htrace : WordTrace (prefixWord ++ tailWord_149048) baseStart_149048 baseEnd_149048 := by
    simpa [prefixWord, tailWord_149048, baseEnd_149048] using wordTrace_append hprefix tailTrace_149048
  have hstable : (prefixWord ++ tailWord_149048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149048).length < 2 ^ (prefixWord ++ tailWord_149048).sum := by decide
  have hdescent : baseEnd_149048 < baseStart_149048 := by decide
  rcases family_descends (prefixWord ++ tailWord_149048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149186 : List Nat := [3, 5, 1, 2, 1, 1, 1, 3, 2, 2, 2]
def baseStart_149186 : Nat := 118140960795 + 149186 * 2 ^ 59
def prefixEnd_149186 : Nat := 4983230072969 + 3 ^ 40 * 149186 * 2
def baseEnd_149186 : Nat := 76604124921758542788913

theorem tailTrace_149186 : CollatzResearch.WordTrace tailWord_149186 prefixEnd_149186 76604124921758542788913 := by
  unfold tailWord_149186
  simp only [CollatzResearch.WordTrace]
  refine ⟨1360315109383018946356853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3627506958354717190284941 1360315109383018946356853)
  ·
    refine ⟨127529541504658026220955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1360315109383018946356853 127529541504658026220955)
    ·
      refine ⟨191294312256987039331433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127529541504658026220955 191294312256987039331433)
      ·
        refine ⟨143470734192740279498575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191294312256987039331433 143470734192740279498575)
        ·
          refine ⟨215206101289110419247863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143470734192740279498575 215206101289110419247863)
          ·
            refine ⟨322809151933665628871795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215206101289110419247863 322809151933665628871795)
            ·
              refine ⟨484213727900498443307693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 322809151933665628871795 484213727900498443307693)
              ·
                refine ⟨181580147962686916240385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 484213727900498443307693 181580147962686916240385)
                ·
                  refine ⟨136185110972015187180289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 181580147962686916240385 136185110972015187180289)
                  ·
                    refine ⟨102138833229011390385217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 136185110972015187180289 102138833229011390385217)
                    ·
                      refine ⟨76604124921758542788913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 102138833229011390385217 76604124921758542788913)
                      ·
                        rfl

theorem cell23_149186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_149186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_149186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_149186 prefixEnd_149186 := by exact prefixLift 149186
  have htrace : WordTrace (prefixWord ++ tailWord_149186) baseStart_149186 baseEnd_149186 := by
    simpa [prefixWord, tailWord_149186, baseEnd_149186] using wordTrace_append hprefix tailTrace_149186
  have hstable : (prefixWord ++ tailWord_149186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149186).length < 2 ^ (prefixWord ++ tailWord_149186).sum := by decide
  have hdescent : baseEnd_149186 < baseStart_149186 := by decide
  rcases family_descends (prefixWord ++ tailWord_149186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149191 : List Nat := [1, 1, 4, 1, 1, 1, 4, 1, 1, 6, 2]
def baseStart_149191 : Nat := 118140960795 + 149191 * 2 ^ 59
def prefixEnd_149191 : Nat := 4983230072969 + 3 ^ 40 * 149191 * 2
def baseEnd_149191 : Nat := 76606692325031023226389

theorem tailTrace_149191 : CollatzResearch.WordTrace tailWord_149191 prefixEnd_149191 76606692325031023226389 := by
  unfold tailWord_149191
  simp only [CollatzResearch.WordTrace]
  refine ⟨5441442802513961639359427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3627628535009307759572951 5441442802513961639359427)
  ·
    refine ⟨8162164203770942459039141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5441442802513961639359427 8162164203770942459039141)
    ·
      refine ⟨1530405788207051711069839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8162164203770942459039141 1530405788207051711069839)
      ·
        refine ⟨2295608682310577566604759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1530405788207051711069839 2295608682310577566604759)
        ·
          refine ⟨3443413023465866349907139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2295608682310577566604759 3443413023465866349907139)
          ·
            refine ⟨5165119535198799524860709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3443413023465866349907139 5165119535198799524860709)
            ·
              refine ⟨968459912849774910911383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5165119535198799524860709 968459912849774910911383)
              ·
                refine ⟨1452689869274662366367075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 968459912849774910911383 1452689869274662366367075)
                ·
                  refine ⟨2179034803911993549550613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1452689869274662366367075 2179034803911993549550613)
                  ·
                    refine ⟨102142256433374697635185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2179034803911993549550613 102142256433374697635185)
                    ·
                      refine ⟨76606692325031023226389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 102142256433374697635185 76606692325031023226389)
                      ·
                        rfl

theorem cell23_149191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 6, 2].length) (baseStart_149191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_149191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_149191 prefixEnd_149191 := by exact prefixLift 149191
  have htrace : WordTrace (prefixWord ++ tailWord_149191) baseStart_149191 baseEnd_149191 := by
    simpa [prefixWord, tailWord_149191, baseEnd_149191] using wordTrace_append hprefix tailTrace_149191
  have hstable : (prefixWord ++ tailWord_149191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149191).length < 2 ^ (prefixWord ++ tailWord_149191).sum := by decide
  have hdescent : baseEnd_149191 < baseStart_149191 := by decide
  rcases family_descends (prefixWord ++ tailWord_149191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149231 : List Nat := [1, 1, 2, 1, 5, 1, 4, 2, 6]
def baseStart_149231 : Nat := 118140960795 + 149231 * 2 ^ 59
def prefixEnd_149231 : Nat := 4983230072969 + 3 ^ 40 * 149231 * 2
def baseEnd_149231 : Nat := 8514136839023429636245

theorem tailTrace_149231 : CollatzResearch.WordTrace tailWord_149231 prefixEnd_149231 8514136839023429636245 := by
  unfold tailWord_149231
  simp only [CollatzResearch.WordTrace]
  refine ⟨5442901722369048470815547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3628601148246032313877031 5442901722369048470815547)
  ·
    refine ⟨8164352583553572706223321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5442901722369048470815547 8164352583553572706223321)
    ·
      refine ⟨6123264437665179529667491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8164352583553572706223321 6123264437665179529667491)
      ·
        refine ⟨9184896656497769294501237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6123264437665179529667491 9184896656497769294501237)
        ·
          refine ⟨861084061546665871359491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9184896656497769294501237 861084061546665871359491)
          ·
            refine ⟨1291626092319998807039237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 861084061546665871359491 1291626092319998807039237)
            ·
              refine ⟨242179892309999776319857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1291626092319998807039237 242179892309999776319857)
              ·
                refine ⟨181634919232499832239893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 242179892309999776319857 181634919232499832239893)
                ·
                  refine ⟨8514136839023429636245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 181634919232499832239893 8514136839023429636245)
                  ·
                    rfl

theorem cell23_149231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 2, 6].length) (baseStart_149231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_149231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_149231 prefixEnd_149231 := by exact prefixLift 149231
  have htrace : WordTrace (prefixWord ++ tailWord_149231) baseStart_149231 baseEnd_149231 := by
    simpa [prefixWord, tailWord_149231, baseEnd_149231] using wordTrace_append hprefix tailTrace_149231
  have hstable : (prefixWord ++ tailWord_149231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149231).length < 2 ^ (prefixWord ++ tailWord_149231).sum := by decide
  have hdescent : baseEnd_149231 < baseStart_149231 := by decide
  rcases family_descends (prefixWord ++ tailWord_149231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149235 : List Nat := [1, 1, 1, 2, 2, 3, 6, 2, 1, 4]
def baseStart_149235 : Nat := 118140960795 + 149235 * 2 ^ 59
def prefixEnd_149235 : Nat := 4983230072969 + 3 ^ 40 * 149235 * 2
def baseEnd_149235 : Nat := 25543095157942950358729

theorem tailTrace_149235 : CollatzResearch.WordTrace tailWord_149235 prefixEnd_149235 25543095157942950358729 := by
  unfold tailWord_149235
  simp only [CollatzResearch.WordTrace]
  refine ⟨5443047614354557153961159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3628698409569704769307439 5443047614354557153961159)
  ·
    refine ⟨8164571421531835730941739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5443047614354557153961159 8164571421531835730941739)
    ·
      refine ⟨12246857132297753596412609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8164571421531835730941739 12246857132297753596412609)
      ·
        refine ⟨9185142849223315197309457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12246857132297753596412609 9185142849223315197309457)
        ·
          refine ⟨6888857136917486397982093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9185142849223315197309457 6888857136917486397982093)
          ·
            refine ⟨2583321426344057399243285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6888857136917486397982093 2583321426344057399243285)
            ·
              refine ⟨121093191859877690589529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2583321426344057399243285 121093191859877690589529)
              ·
                refine ⟨90819893894908267942147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121093191859877690589529 90819893894908267942147)
                ·
                  refine ⟨136229840842362401913221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90819893894908267942147 136229840842362401913221)
                  ·
                    refine ⟨25543095157942950358729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 136229840842362401913221 25543095157942950358729)
                    ·
                      rfl

theorem cell23_149235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 2, 1, 4].length) (baseStart_149235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_149235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_149235 prefixEnd_149235 := by exact prefixLift 149235
  have htrace : WordTrace (prefixWord ++ tailWord_149235) baseStart_149235 baseEnd_149235 := by
    simpa [prefixWord, tailWord_149235, baseEnd_149235] using wordTrace_append hprefix tailTrace_149235
  have hstable : (prefixWord ++ tailWord_149235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149235).length < 2 ^ (prefixWord ++ tailWord_149235).sum := by decide
  have hdescent : baseEnd_149235 < baseStart_149235 := by decide
  rcases family_descends (prefixWord ++ tailWord_149235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149258 : List Nat := [3, 1, 2, 2, 1, 3, 1, 1, 5, 1, 3]
def baseStart_149258 : Nat := 118140960795 + 149258 * 2 ^ 59
def prefixEnd_149258 : Nat := 4983230072969 + 3 ^ 40 * 149258 * 2
def baseEnd_149258 : Nat := 76641095528882261088581

theorem tailTrace_149258 : CollatzResearch.WordTrace tailWord_149258 prefixEnd_149258 76641095528882261088581 := by
  unfold tailWord_149258
  simp only [CollatzResearch.WordTrace]
  refine ⟨1360971623317808020512107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3629257662180821388032285 1360971623317808020512107)
  ·
    refine ⟨2041457434976712030768161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1360971623317808020512107 2041457434976712030768161)
    ·
      refine ⟨1531093076232534023076121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2041457434976712030768161 1531093076232534023076121)
      ·
        refine ⟨1148319807174400517307091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1531093076232534023076121 1148319807174400517307091)
        ·
          refine ⟨1722479710761600775960637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1148319807174400517307091 1722479710761600775960637)
          ·
            refine ⟨645929891535600290985239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1722479710761600775960637 645929891535600290985239)
            ·
              refine ⟨968894837303400436477859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 645929891535600290985239 968894837303400436477859)
              ·
                refine ⟨1453342255955100654716789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 968894837303400436477859 1453342255955100654716789)
                ·
                  refine ⟨136250836495790686379699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1453342255955100654716789 136250836495790686379699)
                  ·
                    refine ⟨204376254743686029569549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 136250836495790686379699 204376254743686029569549)
                    ·
                      refine ⟨76641095528882261088581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 204376254743686029569549 76641095528882261088581)
                      ·
                        rfl

theorem cell23_149258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_149258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_149258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_149258 prefixEnd_149258 := by exact prefixLift 149258
  have htrace : WordTrace (prefixWord ++ tailWord_149258) baseStart_149258 baseEnd_149258 := by
    simpa [prefixWord, tailWord_149258, baseEnd_149258] using wordTrace_append hprefix tailTrace_149258
  have hstable : (prefixWord ++ tailWord_149258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149258).length < 2 ^ (prefixWord ++ tailWord_149258).sum := by decide
  have hdescent : baseEnd_149258 < baseStart_149258 := by decide
  rcases family_descends (prefixWord ++ tailWord_149258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149308 : List Nat := [2, 2, 2, 2, 1, 1, 2, 5, 2, 4]
def baseStart_149308 : Nat := 118140960795 + 149308 * 2 ^ 59
def prefixEnd_149308 : Nat := 4983230072969 + 3 ^ 40 * 149308 * 2
def baseEnd_149308 : Nat := 25555589853869021821117

theorem tailTrace_149308 : CollatzResearch.WordTrace tailWord_149308 prefixEnd_149308 25555589853869021821117 := by
  unfold tailWord_149308
  simp only [CollatzResearch.WordTrace]
  refine ⟨2722855071545045310684289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3630473428726727080912385 2722855071545045310684289)
  ·
    refine ⟨2042141303658783983013217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2722855071545045310684289 2042141303658783983013217)
    ·
      refine ⟨1531605977744087987259913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2042141303658783983013217 1531605977744087987259913)
      ·
        refine ⟨1148704483308065990444935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1531605977744087987259913 1148704483308065990444935)
        ·
          refine ⟨1723056724962098985667403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1148704483308065990444935 1723056724962098985667403)
          ·
            refine ⟨2584585087443148478501105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1723056724962098985667403 2584585087443148478501105)
            ·
              refine ⟨1938438815582361358875829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2584585087443148478501105 1938438815582361358875829)
              ·
                refine ⟨181728638960846377394609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1938438815582361358875829 181728638960846377394609)
                ·
                  refine ⟨136296479220634783045957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 181728638960846377394609 136296479220634783045957)
                  ·
                    refine ⟨25555589853869021821117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 136296479220634783045957 25555589853869021821117)
                    ·
                      rfl

theorem cell23_149308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 5, 2, 4].length) (baseStart_149308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_149308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_149308 prefixEnd_149308 := by exact prefixLift 149308
  have htrace : WordTrace (prefixWord ++ tailWord_149308) baseStart_149308 baseEnd_149308 := by
    simpa [prefixWord, tailWord_149308, baseEnd_149308] using wordTrace_append hprefix tailTrace_149308
  have hstable : (prefixWord ++ tailWord_149308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149308).length < 2 ^ (prefixWord ++ tailWord_149308).sum := by decide
  have hdescent : baseEnd_149308 < baseStart_149308 := by decide
  rcases family_descends (prefixWord ++ tailWord_149308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149315 : List Nat := [1, 1, 1, 3, 1, 5, 2, 2, 3, 2, 2]
def baseStart_149315 : Nat := 118140960795 + 149315 * 2 ^ 59
def prefixEnd_149315 : Nat := 4983230072969 + 3 ^ 40 * 149315 * 2
def baseEnd_149315 : Nat := 76670363926188538075819

theorem tailTrace_149315 : CollatzResearch.WordTrace tailWord_149315 prefixEnd_149315 76670363926188538075819 := by
  unfold tailWord_149315
  simp only [CollatzResearch.WordTrace]
  refine ⟨5445965454064730816873399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3630643636043153877915599 5445965454064730816873399)
  ·
    refine ⟨8168948181097096225310099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5445965454064730816873399 8168948181097096225310099)
    ·
      refine ⟨12253422271645644337965149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8168948181097096225310099 12253422271645644337965149)
      ·
        refine ⟨4595033351867116626736931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12253422271645644337965149 4595033351867116626736931)
        ·
          refine ⟨6892550027800674940105397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4595033351867116626736931 6892550027800674940105397)
          ·
            refine ⟨646176565106313275634881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6892550027800674940105397 646176565106313275634881)
            ·
              refine ⟨484632423829734956726161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 646176565106313275634881 484632423829734956726161)
              ·
                refine ⟨363474317872301217544621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 484632423829734956726161 363474317872301217544621)
                ·
                  refine ⟨136302869202112956579233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 363474317872301217544621 136302869202112956579233)
                  ·
                    refine ⟨102227151901584717434425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 136302869202112956579233 102227151901584717434425)
                    ·
                      refine ⟨76670363926188538075819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 102227151901584717434425 76670363926188538075819)
                      ·
                        rfl

theorem cell23_149315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 3, 2, 2].length) (baseStart_149315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_149315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_149315 prefixEnd_149315 := by exact prefixLift 149315
  have htrace : WordTrace (prefixWord ++ tailWord_149315) baseStart_149315 baseEnd_149315 := by
    simpa [prefixWord, tailWord_149315, baseEnd_149315] using wordTrace_append hprefix tailTrace_149315
  have hstable : (prefixWord ++ tailWord_149315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149315).length < 2 ^ (prefixWord ++ tailWord_149315).sum := by decide
  have hdescent : baseEnd_149315 < baseStart_149315 := by decide
  rcases family_descends (prefixWord ++ tailWord_149315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149325 : List Nat := [1, 6, 1, 2, 1, 1, 1, 2, 4, 4]
def baseStart_149325 : Nat := 118140960795 + 149325 * 2 ^ 59
def prefixEnd_149325 : Nat := 4983230072969 + 3 ^ 40 * 149325 * 2
def baseEnd_149325 : Nat := 25558499577577832983591

theorem tailTrace_149325 : CollatzResearch.WordTrace tailWord_149325 prefixEnd_149325 25558499577577832983591 := by
  unfold tailWord_149325
  simp only [CollatzResearch.WordTrace]
  refine ⟨5446330184028502524737429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3630886789352335016491619 5446330184028502524737429)
  ·
    refine ⟨255296727376336055847067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5446330184028502524737429 255296727376336055847067)
    ·
      refine ⟨382945091064504083770601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255296727376336055847067 382945091064504083770601)
      ·
        refine ⟨287208818298378062827951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 382945091064504083770601 287208818298378062827951)
        ·
          refine ⟨430813227447567094241927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287208818298378062827951 430813227447567094241927)
          ·
            refine ⟨646219841171350641362891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 430813227447567094241927 646219841171350641362891)
            ·
              refine ⟨969329761757025962044337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 646219841171350641362891 969329761757025962044337)
              ·
                refine ⟨726997321317769471533253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 969329761757025962044337 726997321317769471533253)
                ·
                  refine ⟨136311997747081775912485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 726997321317769471533253 136311997747081775912485)
                  ·
                    refine ⟨25558499577577832983591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 136311997747081775912485 25558499577577832983591)
                    ·
                      rfl

theorem cell23_149325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_149325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_149325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_149325 prefixEnd_149325 := by exact prefixLift 149325
  have htrace : WordTrace (prefixWord ++ tailWord_149325) baseStart_149325 baseEnd_149325 := by
    simpa [prefixWord, tailWord_149325, baseEnd_149325] using wordTrace_append hprefix tailTrace_149325
  have hstable : (prefixWord ++ tailWord_149325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149325).length < 2 ^ (prefixWord ++ tailWord_149325).sum := by decide
  have hdescent : baseEnd_149325 < baseStart_149325 := by decide
  rcases family_descends (prefixWord ++ tailWord_149325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149351 : List Nat := [1, 1, 5, 1, 2, 1, 2, 1, 2, 7]
def baseStart_149351 : Nat := 118140960795 + 149351 * 2 ^ 59
def prefixEnd_149351 : Nat := 4983230072969 + 3 ^ 40 * 149351 * 2
def baseEnd_149351 : Nat := 25562949743250132408551

theorem tailTrace_149351 : CollatzResearch.WordTrace tailWord_149351 prefixEnd_149351 25562949743250132408551 := by
  unfold tailWord_149351
  simp only [CollatzResearch.WordTrace]
  refine ⟨5447278481934308965183907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3631518987956205976789271 5447278481934308965183907)
  ·
    refine ⟨8170917722901463447775861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5447278481934308965183907 8170917722901463447775861)
    ·
      refine ⟨766023536522012198228987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8170917722901463447775861 766023536522012198228987)
      ·
        refine ⟨1149035304783018297343481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 766023536522012198228987 1149035304783018297343481)
        ·
          refine ⟨861776478587263723007611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1149035304783018297343481 861776478587263723007611)
          ·
            refine ⟨1292664717880895584511417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 861776478587263723007611 1292664717880895584511417)
            ·
              refine ⟨969498538410671688383563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1292664717880895584511417 969498538410671688383563)
              ·
                refine ⟨1454247807616007532575345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 969498538410671688383563 1454247807616007532575345)
                ·
                  refine ⟨1090685855712005649431509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1454247807616007532575345 1090685855712005649431509)
                  ·
                    refine ⟨25562949743250132408551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1090685855712005649431509 25562949743250132408551)
                    ·
                      rfl

theorem cell23_149351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_149351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_149351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_149351 prefixEnd_149351 := by exact prefixLift 149351
  have htrace : WordTrace (prefixWord ++ tailWord_149351) baseStart_149351 baseEnd_149351 := by
    simpa [prefixWord, tailWord_149351, baseEnd_149351] using wordTrace_append hprefix tailTrace_149351
  have hstable : (prefixWord ++ tailWord_149351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149351).length < 2 ^ (prefixWord ++ tailWord_149351).sum := by decide
  have hdescent : baseEnd_149351 < baseStart_149351 := by decide
  rcases family_descends (prefixWord ++ tailWord_149351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149400 : List Nat := [2, 1, 2, 6, 2, 1, 2, 2, 1, 2, 2]
def baseStart_149400 : Nat := 118140960795 + 149400 * 2 ^ 59
def prefixEnd_149400 : Nat := 4983230072969 + 3 ^ 40 * 149400 * 2
def baseEnd_149400 : Nat := 76714009781820705512929

theorem tailTrace_149400 : CollatzResearch.WordTrace tailWord_149400 prefixEnd_149400 76714009781820705512929 := by
  unfold tailWord_149400
  simp only [CollatzResearch.WordTrace]
  refine ⟨2724532829378395166858827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3632710439171193555811769 2724532829378395166858827)
  ·
    refine ⟨4086799244067592750288241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2724532829378395166858827 4086799244067592750288241)
    ·
      refine ⟨3065099433050694562716181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4086799244067592750288241 3065099433050694562716181)
      ·
        refine ⟨143676535924251307627321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3065099433050694562716181 143676535924251307627321)
        ·
          refine ⟨107757401943188480720491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143676535924251307627321 107757401943188480720491)
          ·
            refine ⟨161636102914782721080737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107757401943188480720491 161636102914782721080737)
            ·
              refine ⟨121227077186087040810553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161636102914782721080737 121227077186087040810553)
              ·
                refine ⟨90920307889565280607915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121227077186087040810553 90920307889565280607915)
                ·
                  refine ⟨136380461834347920911873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90920307889565280607915 136380461834347920911873)
                  ·
                    refine ⟨102285346375760940683905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 136380461834347920911873 102285346375760940683905)
                    ·
                      refine ⟨76714009781820705512929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 102285346375760940683905 76714009781820705512929)
                      ·
                        rfl

theorem cell23_149400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_149400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_149400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_149400 prefixEnd_149400 := by exact prefixLift 149400
  have htrace : WordTrace (prefixWord ++ tailWord_149400) baseStart_149400 baseEnd_149400 := by
    simpa [prefixWord, tailWord_149400, baseEnd_149400] using wordTrace_append hprefix tailTrace_149400
  have hstable : (prefixWord ++ tailWord_149400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149400).length < 2 ^ (prefixWord ++ tailWord_149400).sum := by decide
  have hdescent : baseEnd_149400 < baseStart_149400 := by decide
  rcases family_descends (prefixWord ++ tailWord_149400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149411 : List Nat := [1, 1, 1, 4, 1, 2, 1, 5, 7]
def baseStart_149411 : Nat := 118140960795 + 149411 * 2 ^ 59
def prefixEnd_149411 : Nat := 4983230072969 + 3 ^ 40 * 149411 * 2
def baseEnd_149411 : Nat := 8524406452113351386153

theorem tailTrace_149411 : CollatzResearch.WordTrace tailWord_149411 prefixEnd_149411 8524406452113351386153 := by
  unfold tailWord_149411
  simp only [CollatzResearch.WordTrace]
  refine ⟨5449466861716939212368087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3632977907811292808245391 5449466861716939212368087)
  ·
    refine ⟨8174200292575408818552131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5449466861716939212368087 8174200292575408818552131)
    ·
      refine ⟨12261300438863113227828197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8174200292575408818552131 12261300438863113227828197)
      ·
        refine ⟨2298993832286833730217787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12261300438863113227828197 2298993832286833730217787)
        ·
          refine ⟨3448490748430250595326681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2298993832286833730217787 3448490748430250595326681)
          ·
            refine ⟨2586368061322687946495011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3448490748430250595326681 2586368061322687946495011)
            ·
              refine ⟨3879552091984031919742517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2586368061322687946495011 3879552091984031919742517)
              ·
                refine ⟨363708008623502992475861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3879552091984031919742517 363708008623502992475861)
                ·
                  refine ⟨8524406452113351386153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 363708008623502992475861 8524406452113351386153)
                  ·
                    rfl

theorem cell23_149411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 7].length) (baseStart_149411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_149411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_149411 prefixEnd_149411 := by exact prefixLift 149411
  have htrace : WordTrace (prefixWord ++ tailWord_149411) baseStart_149411 baseEnd_149411 := by
    simpa [prefixWord, tailWord_149411, baseEnd_149411] using wordTrace_append hprefix tailTrace_149411
  have hstable : (prefixWord ++ tailWord_149411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149411).length < 2 ^ (prefixWord ++ tailWord_149411).sum := by decide
  have hdescent : baseEnd_149411 < baseStart_149411 := by decide
  rcases family_descends (prefixWord ++ tailWord_149411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149462 : List Nat := [5, 2, 1, 1, 3, 1, 2, 1, 7]
def baseStart_149462 : Nat := 118140960795 + 149462 * 2 ^ 59
def prefixEnd_149462 : Nat := 4983230072969 + 3 ^ 40 * 149462 * 2
def baseEnd_149462 : Nat := 8527316175822162548627

theorem tailTrace_149462 : CollatzResearch.WordTrace tailWord_149462 prefixEnd_149462 8527316175822162548627 := by
  unfold tailWord_149462
  simp only [CollatzResearch.WordTrace]
  refine ⟨340707936533260932654665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3634217989688116614983093 340707936533260932654665)
  ·
    refine ⟨255530952399945699490999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 340707936533260932654665 255530952399945699490999)
    ·
      refine ⟨383296428599918549236499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255530952399945699490999 383296428599918549236499)
      ·
        refine ⟨574944642899877823854749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 383296428599918549236499 574944642899877823854749)
        ·
          refine ⟨215604241087454183945531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 574944642899877823854749 215604241087454183945531)
          ·
            refine ⟨323406361631181275918297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215604241087454183945531 323406361631181275918297)
            ·
              refine ⟨242554771223385956938723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 323406361631181275918297 242554771223385956938723)
              ·
                refine ⟨363832156835078935408085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 242554771223385956938723 363832156835078935408085)
                ·
                  refine ⟨8527316175822162548627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 363832156835078935408085 8527316175822162548627)
                  ·
                    rfl

theorem cell23_149462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_149462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_149462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_149462 prefixEnd_149462 := by exact prefixLift 149462
  have htrace : WordTrace (prefixWord ++ tailWord_149462) baseStart_149462 baseEnd_149462 := by
    simpa [prefixWord, tailWord_149462, baseEnd_149462] using wordTrace_append hprefix tailTrace_149462
  have hstable : (prefixWord ++ tailWord_149462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149462).length < 2 ^ (prefixWord ++ tailWord_149462).sum := by decide
  have hdescent : baseEnd_149462 < baseStart_149462 := by decide
  rcases family_descends (prefixWord ++ tailWord_149462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149515 : List Nat := [1, 1, 1, 1, 6, 1, 3, 2, 2, 2, 3]
def baseStart_149515 : Nat := 118140960795 + 149515 * 2 ^ 59
def prefixEnd_149515 : Nat := 4983230072969 + 3 ^ 40 * 149515 * 2
def baseEnd_149515 : Nat := 76773060057087755574899

theorem tailTrace_149515 : CollatzResearch.WordTrace tailWord_149515 prefixEnd_149515 76773060057087755574899 := by
  unfold tailWord_149515
  simp only [CollatzResearch.WordTrace]
  refine ⟨5453260053340164974153999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3635506702226776649435999 5453260053340164974153999)
  ·
    refine ⟨8179890080010247461230999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5453260053340164974153999 8179890080010247461230999)
    ·
      refine ⟨12269835120015371191846499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8179890080010247461230999 12269835120015371191846499)
      ·
        refine ⟨18404752680023056787769749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12269835120015371191846499 18404752680023056787769749)
        ·
          refine ⟨862722781876080786926707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 18404752680023056787769749 862722781876080786926707)
          ·
            refine ⟨1294084172814121180390061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 862722781876080786926707 1294084172814121180390061)
            ·
              refine ⟨485281564805295442646273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1294084172814121180390061 485281564805295442646273)
              ·
                refine ⟨363961173603971581984705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 485281564805295442646273 363961173603971581984705)
                ·
                  refine ⟨272970880202978686488529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 363961173603971581984705 272970880202978686488529)
                  ·
                    refine ⟨204728160152234014866397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 272970880202978686488529 204728160152234014866397)
                    ·
                      refine ⟨76773060057087755574899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 204728160152234014866397 76773060057087755574899)
                      ·
                        rfl

theorem cell23_149515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 2, 2, 3].length) (baseStart_149515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_149515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_149515 prefixEnd_149515 := by exact prefixLift 149515
  have htrace : WordTrace (prefixWord ++ tailWord_149515) baseStart_149515 baseEnd_149515 := by
    simpa [prefixWord, tailWord_149515, baseEnd_149515] using wordTrace_append hprefix tailTrace_149515
  have hstable : (prefixWord ++ tailWord_149515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149515).length < 2 ^ (prefixWord ++ tailWord_149515).sum := by decide
  have hdescent : baseEnd_149515 < baseStart_149515 := by decide
  rcases family_descends (prefixWord ++ tailWord_149515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149518 : List Nat := [4, 1, 1, 2, 2, 1, 1, 3, 8]
def baseStart_149518 : Nat := 118140960795 + 149518 * 2 ^ 59
def prefixEnd_149518 : Nat := 4983230072969 + 3 ^ 40 * 149518 * 2
def baseEnd_149518 : Nat := 8530511166561249315265

theorem tailTrace_149518 : CollatzResearch.WordTrace tailWord_149518 prefixEnd_149518 8530511166561249315265 := by
  unfold tailWord_149518
  simp only [CollatzResearch.WordTrace]
  refine ⟨681671184041162060814151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3635579648219530991008805 681671184041162060814151)
  ·
    refine ⟨1022506776061743091221227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 681671184041162060814151 1022506776061743091221227)
    ·
      refine ⟨1533760164092614636831841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1022506776061743091221227 1533760164092614636831841)
      ·
        refine ⟨1150320123069460977623881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1533760164092614636831841 1150320123069460977623881)
        ·
          refine ⟨862740092302095733217911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1150320123069460977623881 862740092302095733217911)
          ·
            refine ⟨1294110138453143599826867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 862740092302095733217911 1294110138453143599826867)
            ·
              refine ⟨1941165207679715399740301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1294110138453143599826867 1941165207679715399740301)
              ·
                refine ⟨727936952879893274902613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1941165207679715399740301 727936952879893274902613)
                ·
                  refine ⟨8530511166561249315265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 727936952879893274902613 8530511166561249315265)
                  ·
                    rfl

theorem cell23_149518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 8].length) (baseStart_149518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_149518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_149518 prefixEnd_149518 := by exact prefixLift 149518
  have htrace : WordTrace (prefixWord ++ tailWord_149518) baseStart_149518 baseEnd_149518 := by
    simpa [prefixWord, tailWord_149518, baseEnd_149518] using wordTrace_append hprefix tailTrace_149518
  have hstable : (prefixWord ++ tailWord_149518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149518).length < 2 ^ (prefixWord ++ tailWord_149518).sum := by decide
  have hdescent : baseEnd_149518 < baseStart_149518 := by decide
  rcases family_descends (prefixWord ++ tailWord_149518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149555 : List Nat := [1, 1, 1, 2, 4, 1, 2, 3, 1, 5, 2]
def baseStart_149555 : Nat := 118140960795 + 149555 * 2 ^ 59
def prefixEnd_149555 : Nat := 4983230072969 + 3 ^ 40 * 149555 * 2
def baseEnd_149555 : Nat := 76793599283267599074715

theorem tailTrace_149555 : CollatzResearch.WordTrace tailWord_149555 prefixEnd_149555 76793599283267599074715 := by
  unfold tailWord_149555
  simp only [CollatzResearch.WordTrace]
  refine ⟨5454718973195251805610119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3636479315463501203740079 5454718973195251805610119)
  ·
    refine ⟨8182078459792877708415179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5454718973195251805610119 8182078459792877708415179)
    ·
      refine ⟨12273117689689316562622769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8182078459792877708415179 12273117689689316562622769)
      ·
        refine ⟨9204838267266987421967077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12273117689689316562622769 9204838267266987421967077)
        ·
          refine ⟨1725907175112560141618827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9204838267266987421967077 1725907175112560141618827)
          ·
            refine ⟨2588860762668840212428241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1725907175112560141618827 2588860762668840212428241)
            ·
              refine ⟨1941645572001630159321181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2588860762668840212428241 1941645572001630159321181)
              ·
                refine ⟨728117089500611309745443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1941645572001630159321181 728117089500611309745443)
                ·
                  refine ⟨1092175634250916964618165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 728117089500611309745443 1092175634250916964618165)
                  ·
                    refine ⟨102391465711023465432953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1092175634250916964618165 102391465711023465432953)
                    ·
                      refine ⟨76793599283267599074715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 102391465711023465432953 76793599283267599074715)
                      ·
                        rfl

theorem cell23_149555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 5, 2].length) (baseStart_149555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_149555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_149555 prefixEnd_149555 := by exact prefixLift 149555
  have htrace : WordTrace (prefixWord ++ tailWord_149555) baseStart_149555 baseEnd_149555 := by
    simpa [prefixWord, tailWord_149555, baseEnd_149555] using wordTrace_append hprefix tailTrace_149555
  have hstable : (prefixWord ++ tailWord_149555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149555).length < 2 ^ (prefixWord ++ tailWord_149555).sum := by decide
  have hdescent : baseEnd_149555 < baseStart_149555 := by decide
  rcases family_descends (prefixWord ++ tailWord_149555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149578 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 5, 6]
def baseStart_149578 : Nat := 118140960795 + 149578 * 2 ^ 59
def prefixEnd_149578 : Nat := 4983230072969 + 3 ^ 40 * 149578 * 2
def baseEnd_149578 : Nat := 25601803112773669695703

theorem tailTrace_149578 : CollatzResearch.WordTrace tailWord_149578 prefixEnd_149578 25601803112773669695703 := by
  unfold tailWord_149578
  simp only [CollatzResearch.WordTrace]
  refine ⟨1363889463027981683424347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3637038568074617822464925 1363889463027981683424347)
  ·
    refine ⟨2045834194541972525136521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1363889463027981683424347 2045834194541972525136521)
    ·
      refine ⟨1534375645906479393852391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2045834194541972525136521 1534375645906479393852391)
      ·
        refine ⟨2301563468859719090778587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1534375645906479393852391 2301563468859719090778587)
        ·
          refine ⟨3452345203289578636167881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2301563468859719090778587 3452345203289578636167881)
          ·
            refine ⟨2589258902467183977125911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3452345203289578636167881 2589258902467183977125911)
            ·
              refine ⟨3883888353700775965688867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2589258902467183977125911 3883888353700775965688867)
              ·
                refine ⟨5825832530551163948533301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3883888353700775965688867 5825832530551163948533301)
                ·
                  refine ⟨546171799739171620174997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5825832530551163948533301 546171799739171620174997)
                  ·
                    refine ⟨25601803112773669695703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 546171799739171620174997 25601803112773669695703)
                    ·
                      rfl

theorem cell23_149578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 5, 6].length) (baseStart_149578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_149578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_149578 prefixEnd_149578 := by exact prefixLift 149578
  have htrace : WordTrace (prefixWord ++ tailWord_149578) baseStart_149578 baseEnd_149578 := by
    simpa [prefixWord, tailWord_149578, baseEnd_149578] using wordTrace_append hprefix tailTrace_149578
  have hstable : (prefixWord ++ tailWord_149578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149578).length < 2 ^ (prefixWord ++ tailWord_149578).sum := by decide
  have hdescent : baseEnd_149578 < baseStart_149578 := by decide
  rcases family_descends (prefixWord ++ tailWord_149578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149585 : List Nat := [1, 2, 2, 1, 3, 1, 1, 2, 2, 6, 2]
def baseStart_149585 : Nat := 118140960795 + 149585 * 2 ^ 59
def prefixEnd_149585 : Nat := 4983230072969 + 3 ^ 40 * 149585 * 2
def baseEnd_149585 : Nat := 76809003702902481699577

theorem tailTrace_149585 : CollatzResearch.WordTrace tailWord_149585 prefixEnd_149585 76809003702902481699577 := by
  unfold tailWord_149585
  simp only [CollatzResearch.WordTrace]
  refine ⟨5455813163086566929202209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3637208775391044619468139 5455813163086566929202209)
  ·
    refine ⟨4091859872314925196901657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5455813163086566929202209 4091859872314925196901657)
    ·
      refine ⟨3068894904236193897676243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4091859872314925196901657 3068894904236193897676243)
      ·
        refine ⟨4603342356354290846514365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3068894904236193897676243 4603342356354290846514365)
        ·
          refine ⟨1726253383632859067442887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4603342356354290846514365 1726253383632859067442887)
          ·
            refine ⟨2589380075449288601164331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1726253383632859067442887 2589380075449288601164331)
            ·
              refine ⟨3884070113173932901746497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2589380075449288601164331 3884070113173932901746497)
              ·
                refine ⟨2913052584880449676309873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3884070113173932901746497 2913052584880449676309873)
                ·
                  refine ⟨2184789438660337257232405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2913052584880449676309873 2184789438660337257232405)
                  ·
                    refine ⟨102412004937203308932769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2184789438660337257232405 102412004937203308932769)
                    ·
                      refine ⟨76809003702902481699577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 102412004937203308932769 76809003702902481699577)
                      ·
                        rfl

theorem cell23_149585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 6, 2].length) (baseStart_149585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_149585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_149585 prefixEnd_149585 := by exact prefixLift 149585
  have htrace : WordTrace (prefixWord ++ tailWord_149585) baseStart_149585 baseEnd_149585 := by
    simpa [prefixWord, tailWord_149585, baseEnd_149585] using wordTrace_append hprefix tailTrace_149585
  have hstable : (prefixWord ++ tailWord_149585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149585).length < 2 ^ (prefixWord ++ tailWord_149585).sum := by decide
  have hdescent : baseEnd_149585 < baseStart_149585 := by decide
  rcases family_descends (prefixWord ++ tailWord_149585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149615 : List Nat := [1, 1, 2, 1, 3, 4, 2, 2, 1, 2, 4]
def baseStart_149615 : Nat := 118140960795 + 149615 * 2 ^ 59
def prefixEnd_149615 : Nat := 4983230072969 + 3 ^ 40 * 149615 * 2
def baseEnd_149615 : Nat := 76824408122537364324439

theorem tailTrace_149615 : CollatzResearch.WordTrace tailWord_149615 prefixEnd_149615 76824408122537364324439 := by
  unfold tailWord_149615
  simp only [CollatzResearch.WordTrace]
  refine ⟨5456907352977882052794299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3637938235318588035196199 5456907352977882052794299)
  ·
    refine ⟨8185361029466823079191449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5456907352977882052794299 8185361029466823079191449)
    ·
      refine ⟨6139020772100117309393587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8185361029466823079191449 6139020772100117309393587)
      ·
        refine ⟨9208531158150175964090381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6139020772100117309393587 9208531158150175964090381)
        ·
          refine ⟨3453199184306315986533893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9208531158150175964090381 3453199184306315986533893)
          ·
            refine ⟨647474847057434247475105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3453199184306315986533893 647474847057434247475105)
            ·
              refine ⟨485606135293075685606329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 647474847057434247475105 485606135293075685606329)
              ·
                refine ⟨364204601469806764204747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 485606135293075685606329 364204601469806764204747)
                ·
                  refine ⟨546306902204710146307121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 364204601469806764204747 546306902204710146307121)
                  ·
                    refine ⟨409730176653532609730341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 546306902204710146307121 409730176653532609730341)
                    ·
                      refine ⟨76824408122537364324439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 409730176653532609730341 76824408122537364324439)
                      ·
                        rfl

theorem cell23_149615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 2, 4].length) (baseStart_149615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_149615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_149615 prefixEnd_149615 := by exact prefixLift 149615
  have htrace : WordTrace (prefixWord ++ tailWord_149615) baseStart_149615 baseEnd_149615 := by
    simpa [prefixWord, tailWord_149615, baseEnd_149615] using wordTrace_append hprefix tailTrace_149615
  have hstable : (prefixWord ++ tailWord_149615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149615).length < 2 ^ (prefixWord ++ tailWord_149615).sum := by decide
  have hdescent : baseEnd_149615 < baseStart_149615 := by decide
  rcases family_descends (prefixWord ++ tailWord_149615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149629 : List Nat := [1, 4, 1, 1, 3, 4, 1, 2, 2, 4]
def baseStart_149629 : Nat := 118140960795 + 149629 * 2 ^ 59
def prefixEnd_149629 : Nat := 4983230072969 + 3 ^ 40 * 149629 * 2
def baseEnd_149629 : Nat := 25610532283900103183125

theorem tailTrace_149629 : CollatzResearch.WordTrace tailWord_149629 prefixEnd_149629 25610532283900103183125 := by
  unfold tailWord_149629
  simp only [CollatzResearch.WordTrace]
  refine ⟨5457417974927162443803941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3638278649951441629202627 5457417974927162443803941)
  ·
    refine ⟨1023265870298842958213239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5457417974927162443803941 1023265870298842958213239)
    ·
      refine ⟨1534898805448264437319859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1023265870298842958213239 1534898805448264437319859)
      ·
        refine ⟨2302348208172396655979789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1534898805448264437319859 2302348208172396655979789)
        ·
          refine ⟨863380578064648745992421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2302348208172396655979789 863380578064648745992421)
          ·
            refine ⟨161883858387121639873579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 863380578064648745992421 161883858387121639873579)
            ·
              refine ⟨242825787580682459810369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161883858387121639873579 242825787580682459810369)
              ·
                refine ⟨182119340685511844857777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 242825787580682459810369 182119340685511844857777)
                ·
                  refine ⟨136589505514133883643333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 182119340685511844857777 136589505514133883643333)
                  ·
                    refine ⟨25610532283900103183125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 136589505514133883643333 25610532283900103183125)
                    ·
                      rfl

theorem cell23_149629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 2, 2, 4].length) (baseStart_149629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_149629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_149629 prefixEnd_149629 := by exact prefixLift 149629
  have htrace : WordTrace (prefixWord ++ tailWord_149629) baseStart_149629 baseEnd_149629 := by
    simpa [prefixWord, tailWord_149629, baseEnd_149629] using wordTrace_append hprefix tailTrace_149629
  have hstable : (prefixWord ++ tailWord_149629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149629).length < 2 ^ (prefixWord ++ tailWord_149629).sum := by decide
  have hdescent : baseEnd_149629 < baseStart_149629 := by decide
  rcases family_descends (prefixWord ++ tailWord_149629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149636 : List Nat := [2, 3, 2, 1, 2, 1, 1, 6, 1, 2, 2]
def baseStart_149636 : Nat := 118140960795 + 149636 * 2 ^ 59
def prefixEnd_149636 : Nat := 4983230072969 + 3 ^ 40 * 149636 * 2
def baseEnd_149636 : Nat := 76835191216281782161843

theorem tailTrace_149636 : CollatzResearch.WordTrace tailWord_149636 prefixEnd_149636 76835191216281782161843 := by
  unfold tailWord_149636
  simp only [CollatzResearch.WordTrace]
  refine ⟨2728836642950901319654381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3638448857267868426205841 2728836642950901319654381)
  ·
    refine ⟨1023313741106587994870393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2728836642950901319654381 1023313741106587994870393)
    ·
      refine ⟨767485305829940996152795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1023313741106587994870393 767485305829940996152795)
      ·
        refine ⟨1151227958744911494229193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 767485305829940996152795 1151227958744911494229193)
        ·
          refine ⟨863420969058683620671895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1151227958744911494229193 863420969058683620671895)
          ·
            refine ⟨1295131453588025431007843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 863420969058683620671895 1295131453588025431007843)
            ·
              refine ⟨1942697180382038146511765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1295131453588025431007843 1942697180382038146511765)
              ·
                refine ⟨91063930330408038117739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1942697180382038146511765 91063930330408038117739)
                ·
                  refine ⟨136595895495612057176609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91063930330408038117739 136595895495612057176609)
                  ·
                    refine ⟨102446921621709042882457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 136595895495612057176609 102446921621709042882457)
                    ·
                      refine ⟨76835191216281782161843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 102446921621709042882457 76835191216281782161843)
                      ·
                        rfl

theorem cell23_149636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 6, 1, 2, 2].length) (baseStart_149636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_149636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_149636 prefixEnd_149636 := by exact prefixLift 149636
  have htrace : WordTrace (prefixWord ++ tailWord_149636) baseStart_149636 baseEnd_149636 := by
    simpa [prefixWord, tailWord_149636, baseEnd_149636] using wordTrace_append hprefix tailTrace_149636
  have hstable : (prefixWord ++ tailWord_149636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149636).length < 2 ^ (prefixWord ++ tailWord_149636).sum := by decide
  have hdescent : baseEnd_149636 < baseStart_149636 := by decide
  rcases family_descends (prefixWord ++ tailWord_149636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149646 : List Nat := [4, 1, 1, 3, 3, 1, 3, 1, 2, 4]
def baseStart_149646 : Nat := 118140960795 + 149646 * 2 ^ 59
def prefixEnd_149646 : Nat := 4983230072969 + 3 ^ 40 * 149646 * 2
def baseEnd_149646 : Nat := 25613442007608914345599

theorem tailTrace_149646 : CollatzResearch.WordTrace tailWord_149646 prefixEnd_149646 25613442007608914345599 := by
  unfold tailWord_149646
  simp only [CollatzResearch.WordTrace]
  refine ⟨682254751983196793396599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3638692010577049564781861 682254751983196793396599)
  ·
    refine ⟨1023382127974795190094899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 682254751983196793396599 1023382127974795190094899)
    ·
      refine ⟨1535073191962192785142349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1023382127974795190094899 1535073191962192785142349)
      ·
        refine ⟨575652446985822294428381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1535073191962192785142349 575652446985822294428381)
        ·
          refine ⟨215869667619683360410643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 575652446985822294428381 215869667619683360410643)
          ·
            refine ⟨323804501429525040615965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215869667619683360410643 323804501429525040615965)
            ·
              refine ⟨121426688036071890230987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 323804501429525040615965 121426688036071890230987)
              ·
                refine ⟨182140032054107835346481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121426688036071890230987 182140032054107835346481)
                ·
                  refine ⟨136605024040580876509861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 182140032054107835346481 136605024040580876509861)
                  ·
                    refine ⟨25613442007608914345599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 136605024040580876509861 25613442007608914345599)
                    ·
                      rfl

theorem cell23_149646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 1, 2, 4].length) (baseStart_149646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_149646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_149646 prefixEnd_149646 := by exact prefixLift 149646
  have htrace : WordTrace (prefixWord ++ tailWord_149646) baseStart_149646 baseEnd_149646 := by
    simpa [prefixWord, tailWord_149646, baseEnd_149646] using wordTrace_append hprefix tailTrace_149646
  have hstable : (prefixWord ++ tailWord_149646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149646).length < 2 ^ (prefixWord ++ tailWord_149646).sum := by decide
  have hdescent : baseEnd_149646 < baseStart_149646 := by decide
  rcases family_descends (prefixWord ++ tailWord_149646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149665 : List Nat := [1, 2, 3, 3, 1, 2, 1, 1, 2, 2, 5]
def baseStart_149665 : Nat := 118140960795 + 149665 * 2 ^ 59
def prefixEnd_149665 : Nat := 4983230072969 + 3 ^ 40 * 149665 * 2
def baseEnd_149665 : Nat := 76850082155262168699209

theorem tailTrace_149665 : CollatzResearch.WordTrace tailWord_149665 prefixEnd_149665 76850082155262168699209 := by
  unfold tailWord_149665
  simp only [CollatzResearch.WordTrace]
  refine ⟨5458731002796740592114449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3639154001864493728076299 5458731002796740592114449)
  ·
    refine ⟨4094048252097555444085837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5458731002796740592114449 4094048252097555444085837)
    ·
      refine ⟨1535268094536583291532189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4094048252097555444085837 1535268094536583291532189)
      ·
        refine ⟨575725535451218734324571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1535268094536583291532189 575725535451218734324571)
        ·
          refine ⟨863588303176828101486857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 575725535451218734324571 863588303176828101486857)
          ·
            refine ⟨647691227382621076115143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 863588303176828101486857 647691227382621076115143)
            ·
              refine ⟨971536841073931614172715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 647691227382621076115143 971536841073931614172715)
              ·
                refine ⟨1457305261610897421259073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 971536841073931614172715 1457305261610897421259073)
                ·
                  refine ⟨1092978946208173065944305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1457305261610897421259073 1092978946208173065944305)
                  ·
                    refine ⟨819734209656129799458229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1092978946208173065944305 819734209656129799458229)
                    ·
                      refine ⟨76850082155262168699209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 819734209656129799458229 76850082155262168699209)
                      ·
                        rfl

theorem cell23_149665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_149665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_149665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_149665 prefixEnd_149665 := by exact prefixLift 149665
  have htrace : WordTrace (prefixWord ++ tailWord_149665) baseStart_149665 baseEnd_149665 := by
    simpa [prefixWord, tailWord_149665, baseEnd_149665] using wordTrace_append hprefix tailTrace_149665
  have hstable : (prefixWord ++ tailWord_149665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149665).length < 2 ^ (prefixWord ++ tailWord_149665).sum := by decide
  have hdescent : baseEnd_149665 < baseStart_149665 := by decide
  rcases family_descends (prefixWord ++ tailWord_149665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149695 : List Nat := [1, 1, 2, 2, 2, 2, 1, 3, 2, 4, 3]
def baseStart_149695 : Nat := 118140960795 + 149695 * 2 ^ 59
def prefixEnd_149695 : Nat := 4983230072969 + 3 ^ 40 * 149695 * 2
def baseEnd_149695 : Nat := 76865486574897051324071

theorem tailTrace_149695 : CollatzResearch.WordTrace tailWord_149695 prefixEnd_149695 76865486574897051324071 := by
  unfold tailWord_149695
  simp only [CollatzResearch.WordTrace]
  refine ⟨5459825192688055715706539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3639883461792037143804359 5459825192688055715706539)
  ·
    refine ⟨8189737789032083573559809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5459825192688055715706539 8189737789032083573559809)
    ·
      refine ⟨6142303341774062680169857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8189737789032083573559809 6142303341774062680169857)
      ·
        refine ⟨4606727506330547010127393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6142303341774062680169857 4606727506330547010127393)
        ·
          refine ⟨3455045629747910257595545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4606727506330547010127393 3455045629747910257595545)
          ·
            refine ⟨2591284222310932693196659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3455045629747910257595545 2591284222310932693196659)
            ·
              refine ⟨3886926333466399039794989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2591284222310932693196659 3886926333466399039794989)
              ·
                refine ⟨1457597375049899639923121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3886926333466399039794989 1457597375049899639923121)
                ·
                  refine ⟨1093198031287424729942341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1457597375049899639923121 1093198031287424729942341)
                  ·
                    refine ⟨204974630866392136864189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1093198031287424729942341 204974630866392136864189)
                    ·
                      refine ⟨76865486574897051324071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 204974630866392136864189 76865486574897051324071)
                      ·
                        rfl

theorem cell23_149695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 4, 3].length) (baseStart_149695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_149695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_149695 prefixEnd_149695 := by exact prefixLift 149695
  have htrace : WordTrace (prefixWord ++ tailWord_149695) baseStart_149695 baseEnd_149695 := by
    simpa [prefixWord, tailWord_149695, baseEnd_149695] using wordTrace_append hprefix tailTrace_149695
  have hstable : (prefixWord ++ tailWord_149695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149695).length < 2 ^ (prefixWord ++ tailWord_149695).sum := by decide
  have hdescent : baseEnd_149695 < baseStart_149695 := by decide
  rcases family_descends (prefixWord ++ tailWord_149695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149732 : List Nat := [2, 3, 1, 1, 1, 2, 1, 7, 5]
def baseStart_149732 : Nat := 118140960795 + 149732 * 2 ^ 59
def prefixEnd_149732 : Nat := 4983230072969 + 3 ^ 40 * 149732 * 2
def baseEnd_149732 : Nat := 8542720595457045173489

theorem tailTrace_149732 : CollatzResearch.WordTrace tailWord_149732 prefixEnd_149732 8542720595457045173489 := by
  unfold tailWord_149732
  simp only [CollatzResearch.WordTrace]
  refine ⟨2730587346777005517401725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3640783129036007356535633 2730587346777005517401725)
  ·
    refine ⟨1023970255041377069025647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2730587346777005517401725 1023970255041377069025647)
    ·
      refine ⟨1535955382562065603538471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1023970255041377069025647 1535955382562065603538471)
      ·
        refine ⟨2303933073843098405307707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1535955382562065603538471 2303933073843098405307707)
        ·
          refine ⟨3455899610764647607961561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2303933073843098405307707 3455899610764647607961561)
          ·
            refine ⟨2591924708073485705971171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3455899610764647607961561 2591924708073485705971171)
            ·
              refine ⟨3887887062110228558956757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2591924708073485705971171 3887887062110228558956757)
              ·
                refine ⟨91122353018208481850549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3887887062110228558956757 91122353018208481850549)
                ·
                  refine ⟨8542720595457045173489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 91122353018208481850549 8542720595457045173489)
                  ·
                    rfl

theorem cell23_149732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 7, 5].length) (baseStart_149732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_149732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_149732 prefixEnd_149732 := by exact prefixLift 149732
  have htrace : WordTrace (prefixWord ++ tailWord_149732) baseStart_149732 baseEnd_149732 := by
    simpa [prefixWord, tailWord_149732, baseEnd_149732] using wordTrace_append hprefix tailTrace_149732
  have hstable : (prefixWord ++ tailWord_149732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149732).length < 2 ^ (prefixWord ++ tailWord_149732).sum := by decide
  have hdescent : baseEnd_149732 < baseStart_149732 := by decide
  rcases family_descends (prefixWord ++ tailWord_149732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149742 : List Nat := [4, 1, 2, 1, 1, 1, 1, 4, 2, 3, 3]
def baseStart_149742 : Nat := 118140960795 + 149742 * 2 ^ 59
def prefixEnd_149742 : Nat := 4983230072969 + 3 ^ 40 * 149742 * 2
def baseEnd_149742 : Nat := 76889620165658367436355

theorem tailTrace_149742 : CollatzResearch.WordTrace tailWord_149742 prefixEnd_149742 76889620165658367436355 := by
  unfold tailWord_149742
  simp only [CollatzResearch.WordTrace]
  refine ⟨682692427939722842833435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3641026282345188495111653 682692427939722842833435)
  ·
    refine ⟨1024038641909584264250153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 682692427939722842833435 1024038641909584264250153)
    ·
      refine ⟨768028981432188198187615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1024038641909584264250153 768028981432188198187615)
      ·
        refine ⟨1152043472148282297281423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 768028981432188198187615 1152043472148282297281423)
        ·
          refine ⟨1728065208222423445922135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1152043472148282297281423 1728065208222423445922135)
          ·
            refine ⟨2592097812333635168883203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1728065208222423445922135 2592097812333635168883203)
            ·
              refine ⟨3888146718500452753324805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2592097812333635168883203 3888146718500452753324805)
              ·
                refine ⟨729027509718834891248401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3888146718500452753324805 729027509718834891248401)
                ·
                  refine ⟨546770632289126168436301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 729027509718834891248401 546770632289126168436301)
                  ·
                    refine ⟨205038987108422313163613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 546770632289126168436301 205038987108422313163613)
                    ·
                      refine ⟨76889620165658367436355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 205038987108422313163613 76889620165658367436355)
                      ·
                        rfl

theorem cell23_149742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_149742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_149742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_149742 prefixEnd_149742 := by exact prefixLift 149742
  have htrace : WordTrace (prefixWord ++ tailWord_149742) baseStart_149742 baseEnd_149742 := by
    simpa [prefixWord, tailWord_149742, baseEnd_149742] using wordTrace_append hprefix tailTrace_149742
  have hstable : (prefixWord ++ tailWord_149742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149742).length < 2 ^ (prefixWord ++ tailWord_149742).sum := by decide
  have hdescent : baseEnd_149742 < baseStart_149742 := by decide
  rcases family_descends (prefixWord ++ tailWord_149742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149795 : List Nat := [1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 6]
def baseStart_149795 : Nat := 118140960795 + 149795 * 2 ^ 59
def prefixEnd_149795 : Nat := 4983230072969 + 3 ^ 40 * 149795 * 2
def baseEnd_149795 : Nat := 76916834640346660073611

theorem tailTrace_149795 : CollatzResearch.WordTrace tailWord_149795 prefixEnd_149795 76916834640346660073611 := by
  unfold tailWord_149795
  simp only [CollatzResearch.WordTrace]
  refine ⟨5463472492325772794346839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3642314994883848529564559 5463472492325772794346839)
  ·
    refine ⟨8195208738488659191520259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5463472492325772794346839 8195208738488659191520259)
    ·
      refine ⟨12292813107732988787280389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8195208738488659191520259 12292813107732988787280389)
      ·
        refine ⟨2304902457699935397615073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12292813107732988787280389 2304902457699935397615073)
        ·
          refine ⟨1728676843274951548211305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2304902457699935397615073 1728676843274951548211305)
          ·
            refine ⟨1296507632456213661158479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1728676843274951548211305 1296507632456213661158479)
            ·
              refine ⟨1944761448684320491737719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1296507632456213661158479 1944761448684320491737719)
              ·
                refine ⟨2917142173026480737606579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1944761448684320491737719 2917142173026480737606579)
                ·
                  refine ⟨4375713259539721106409869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2917142173026480737606579 4375713259539721106409869)
                  ·
                    refine ⟨1640892472327395414903701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4375713259539721106409869 1640892472327395414903701)
                    ·
                      refine ⟨76916834640346660073611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1640892472327395414903701 76916834640346660073611)
                      ·
                        rfl

theorem cell23_149795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_149795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_149795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_149795 prefixEnd_149795 := by exact prefixLift 149795
  have htrace : WordTrace (prefixWord ++ tailWord_149795) baseStart_149795 baseEnd_149795 := by
    simpa [prefixWord, tailWord_149795, baseEnd_149795] using wordTrace_append hprefix tailTrace_149795
  have hstable : (prefixWord ++ tailWord_149795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149795).length < 2 ^ (prefixWord ++ tailWord_149795).sum := by decide
  have hdescent : baseEnd_149795 < baseStart_149795 := by decide
  rcases family_descends (prefixWord ++ tailWord_149795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149912 : List Nat := [2, 1, 2, 5, 1, 12]
def baseStart_149912 : Nat := 118140960795 + 149912 * 2 ^ 59
def prefixEnd_149912 : Nat := 4983230072969 + 3 ^ 40 * 149912 * 2
def baseEnd_149912 : Nat := 316777415131369145311

theorem tailTrace_149912 : CollatzResearch.WordTrace tailWord_149912 prefixEnd_149912 316777415131369145311 := by
  unfold tailWord_149912
  simp only [CollatzResearch.WordTrace]
  refine ⟨2733869916450950888177995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3645159888601267850903993 2733869916450950888177995)
  ·
    refine ⟨4100804874676426332266993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2733869916450950888177995 4100804874676426332266993)
    ·
      refine ⟨3075603656007319749200245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4100804874676426332266993 3075603656007319749200245)
      ·
        refine ⟨288337842750686226487523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3075603656007319749200245 288337842750686226487523)
        ·
          refine ⟨432506764126029339731285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288337842750686226487523 432506764126029339731285)
          ·
            refine ⟨316777415131369145311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 432506764126029339731285 316777415131369145311)
            ·
              rfl

theorem cell23_149912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 12].length) (baseStart_149912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_149912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_149912 prefixEnd_149912 := by exact prefixLift 149912
  have htrace : WordTrace (prefixWord ++ tailWord_149912) baseStart_149912 baseEnd_149912 := by
    simpa [prefixWord, tailWord_149912, baseEnd_149912] using wordTrace_append hprefix tailTrace_149912
  have hstable : (prefixWord ++ tailWord_149912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149912).length < 2 ^ (prefixWord ++ tailWord_149912).sum := by decide
  have hdescent : baseEnd_149912 < baseStart_149912 := by decide
  rcases family_descends (prefixWord ++ tailWord_149912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149917 : List Nat := [1, 4, 2, 1, 4, 2, 2, 2, 1, 1, 3]
def baseStart_149917 : Nat := 118140960795 + 149917 * 2 ^ 59
def prefixEnd_149917 : Nat := 4983230072969 + 3 ^ 40 * 149917 * 2
def baseEnd_149917 : Nat := 76979479280195182748051

theorem tailTrace_149917 : CollatzResearch.WordTrace tailWord_149917 prefixEnd_149917 76979479280195182748051 := by
  unfold tailWord_149917
  simp only [CollatzResearch.WordTrace]
  refine ⟨5467922197883787630288005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3645281465255858420192003 5467922197883787630288005)
  ·
    refine ⟨1025235412103210180679001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5467922197883787630288005 1025235412103210180679001)
    ·
      refine ⟨768926559077407635509251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1025235412103210180679001 768926559077407635509251)
      ·
        refine ⟨1153389838616111453263877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 768926559077407635509251 1153389838616111453263877)
        ·
          refine ⟨216260594740520897486977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1153389838616111453263877 216260594740520897486977)
          ·
            refine ⟨162195446055390673115233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216260594740520897486977 162195446055390673115233)
            ·
              refine ⟨121646584541543004836425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162195446055390673115233 121646584541543004836425)
              ·
                refine ⟨91234938406157253627319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121646584541543004836425 91234938406157253627319)
                ·
                  refine ⟨136852407609235880440979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91234938406157253627319 136852407609235880440979)
                  ·
                    refine ⟨205278611413853820661469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 136852407609235880440979 205278611413853820661469)
                    ·
                      refine ⟨76979479280195182748051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 205278611413853820661469 76979479280195182748051)
                      ·
                        rfl

theorem cell23_149917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 2, 1, 1, 3].length) (baseStart_149917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_149917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_149917 prefixEnd_149917 := by exact prefixLift 149917
  have htrace : WordTrace (prefixWord ++ tailWord_149917) baseStart_149917 baseEnd_149917 := by
    simpa [prefixWord, tailWord_149917, baseEnd_149917] using wordTrace_append hprefix tailTrace_149917
  have hstable : (prefixWord ++ tailWord_149917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149917).length < 2 ^ (prefixWord ++ tailWord_149917).sum := by decide
  have hdescent : baseEnd_149917 < baseStart_149917 := by decide
  rcases family_descends (prefixWord ++ tailWord_149917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149939 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 8, 1, 3]
def baseStart_149939 : Nat := 118140960795 + 149939 * 2 ^ 59
def prefixEnd_149939 : Nat := 4983230072969 + 3 ^ 40 * 149939 * 2
def baseEnd_149939 : Nat := 76990775854594096672949

theorem tailTrace_149939 : CollatzResearch.WordTrace tailWord_149939 prefixEnd_149939 76990775854594096672949 := by
  unfold tailWord_149939
  simp only [CollatzResearch.WordTrace]
  refine ⟨5468724603804085387588871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3645816402536056925059247 5468724603804085387588871)
  ·
    refine ⟨8203086905706128081383307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5468724603804085387588871 8203086905706128081383307)
    ·
      refine ⟨12304630358559192122074961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8203086905706128081383307 12304630358559192122074961)
      ·
        refine ⟨9228472768919394091556221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12304630358559192122074961 9228472768919394091556221)
        ·
          refine ⟨3460677288344772784333583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9228472768919394091556221 3460677288344772784333583)
          ·
            refine ⟨5191015932517159176500375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3460677288344772784333583 5191015932517159176500375)
            ·
              refine ⟨7786523898775738764750563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5191015932517159176500375 7786523898775738764750563)
              ·
                refine ⟨11679785848163608147125845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7786523898775738764750563 11679785848163608147125845)
                ·
                  refine ⟨136872490408167282974131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11679785848163608147125845 136872490408167282974131)
                  ·
                    refine ⟨205308735612250924461197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 136872490408167282974131 205308735612250924461197)
                    ·
                      refine ⟨76990775854594096672949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 205308735612250924461197 76990775854594096672949)
                      ·
                        rfl

theorem cell23_149939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 8, 1, 3].length) (baseStart_149939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_149939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_149939 prefixEnd_149939 := by exact prefixLift 149939
  have htrace : WordTrace (prefixWord ++ tailWord_149939) baseStart_149939 baseEnd_149939 := by
    simpa [prefixWord, tailWord_149939, baseEnd_149939] using wordTrace_append hprefix tailTrace_149939
  have hstable : (prefixWord ++ tailWord_149939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149939).length < 2 ^ (prefixWord ++ tailWord_149939).sum := by decide
  have hdescent : baseEnd_149939 < baseStart_149939 := by decide
  rcases family_descends (prefixWord ++ tailWord_149939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149952 : List Nat := [2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 5]
def baseStart_149952 : Nat := 118140960795 + 149952 * 2 ^ 59
def prefixEnd_149952 : Nat := 4983230072969 + 3 ^ 40 * 149952 * 2
def baseEnd_149952 : Nat := 76997451103102545810389

theorem tailTrace_149952 : CollatzResearch.WordTrace tailWord_149952 prefixEnd_149952 76997451103102545810389 := by
  unfold tailWord_149952
  simp only [CollatzResearch.WordTrace]
  refine ⟨2734599376378494303906055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3646132501837992405208073 2734599376378494303906055)
  ·
    refine ⟨4101899064567741455859083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2734599376378494303906055 4101899064567741455859083)
    ·
      refine ⟨6152848596851612183788625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4101899064567741455859083 6152848596851612183788625)
      ·
        refine ⟨4614636447638709137841469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6152848596851612183788625 4614636447638709137841469)
        ·
          refine ⟨1730488667864515926690551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4614636447638709137841469 1730488667864515926690551)
          ·
            refine ⟨2595733001796773890035827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1730488667864515926690551 2595733001796773890035827)
            ·
              refine ⟨3893599502695160835053741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2595733001796773890035827 3893599502695160835053741)
              ·
                refine ⟨1460099813510685313145153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3893599502695160835053741 1460099813510685313145153)
                ·
                  refine ⟨1095074860133013984858865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1460099813510685313145153 1095074860133013984858865)
                  ·
                    refine ⟨821306145099760488644149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1095074860133013984858865 821306145099760488644149)
                    ·
                      refine ⟨76997451103102545810389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 821306145099760488644149 76997451103102545810389)
                      ·
                        rfl

theorem cell23_149952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 5].length) (baseStart_149952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_149952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_149952 prefixEnd_149952 := by exact prefixLift 149952
  have htrace : WordTrace (prefixWord ++ tailWord_149952) baseStart_149952 baseEnd_149952 := by
    simpa [prefixWord, tailWord_149952, baseEnd_149952] using wordTrace_append hprefix tailTrace_149952
  have hstable : (prefixWord ++ tailWord_149952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149952).length < 2 ^ (prefixWord ++ tailWord_149952).sum := by decide
  have hdescent : baseEnd_149952 < baseStart_149952 := by decide
  rcases family_descends (prefixWord ++ tailWord_149952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149973 : List Nat := [1, 3, 2, 3, 1, 2, 3, 2, 2, 1, 3]
def baseStart_149973 : Nat := 118140960795 + 149973 * 2 ^ 59
def prefixEnd_149973 : Nat := 4983230072969 + 3 ^ 40 * 149973 * 2
def baseEnd_149973 : Nat := 77008234196846963647793

theorem tailTrace_149973 : CollatzResearch.WordTrace tailWord_149973 prefixEnd_149973 77008234196846963647793 := by
  unfold tailWord_149973
  simp only [CollatzResearch.WordTrace]
  refine ⟨5469964685680909194326573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3646643123787272796217715 5469964685680909194326573)
  ·
    refine ⟨2051236757130340947872465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5469964685680909194326573 2051236757130340947872465)
    ·
      refine ⟨1538427567847755710904349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2051236757130340947872465 1538427567847755710904349)
      ·
        refine ⟨576910337942908391589131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1538427567847755710904349 576910337942908391589131)
        ·
          refine ⟨865365506914362587383697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 576910337942908391589131 865365506914362587383697)
          ·
            refine ⟨649024130185771940537773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 865365506914362587383697 649024130185771940537773)
            ·
              refine ⟨243384048819664477701665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 649024130185771940537773 243384048819664477701665)
              ·
                refine ⟨182538036614748358276249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 243384048819664477701665 182538036614748358276249)
                ·
                  refine ⟨136903527461061268707187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 182538036614748358276249 136903527461061268707187)
                  ·
                    refine ⟨205355291191591903060781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 136903527461061268707187 205355291191591903060781)
                    ·
                      refine ⟨77008234196846963647793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 205355291191591903060781 77008234196846963647793)
                      ·
                        rfl

theorem cell23_149973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_149973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_149973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_149973 prefixEnd_149973 := by exact prefixLift 149973
  have htrace : WordTrace (prefixWord ++ tailWord_149973) baseStart_149973 baseEnd_149973 := by
    simpa [prefixWord, tailWord_149973, baseEnd_149973] using wordTrace_append hprefix tailTrace_149973
  have hstable : (prefixWord ++ tailWord_149973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149973).length < 2 ^ (prefixWord ++ tailWord_149973).sum := by decide
  have hdescent : baseEnd_149973 < baseStart_149973 := by decide
  rcases family_descends (prefixWord ++ tailWord_149973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150049 : List Nat := [1, 2, 3, 2, 2, 1, 1, 2, 4, 5]
def baseStart_150049 : Nat := 118140960795 + 150049 * 2 ^ 59
def prefixEnd_150049 : Nat := 4983230072969 + 3 ^ 40 * 150049 * 2
def baseEnd_150049 : Nat := 25682419575529555432481

theorem tailTrace_150049 : CollatzResearch.WordTrace tailWord_150049 prefixEnd_150049 25682419575529555432481 := by
  unfold tailWord_150049
  simp only [CollatzResearch.WordTrace]
  refine ⟨5472736633405574174093201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3648491088937049449395467 5472736633405574174093201)
  ·
    refine ⟨4104552475054180630569901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5472736633405574174093201 4104552475054180630569901)
    ·
      refine ⟨1539207178145317736463713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4104552475054180630569901 1539207178145317736463713)
      ·
        refine ⟨1154405383608988302347785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1539207178145317736463713 1154405383608988302347785)
        ·
          refine ⟨865804037706741226760839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1154405383608988302347785 865804037706741226760839)
          ·
            refine ⟨1298706056560111840141259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 865804037706741226760839 1298706056560111840141259)
            ·
              refine ⟨1948059084840167760211889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1298706056560111840141259 1948059084840167760211889)
              ·
                refine ⟨1461044313630125820158917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1948059084840167760211889 1461044313630125820158917)
                ·
                  refine ⟨273945808805648591279797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1461044313630125820158917 273945808805648591279797)
                  ·
                    refine ⟨25682419575529555432481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 273945808805648591279797 25682419575529555432481)
                    ·
                      rfl

theorem cell23_150049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 4, 5].length) (baseStart_150049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_150049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_150049 prefixEnd_150049 := by exact prefixLift 150049
  have htrace : WordTrace (prefixWord ++ tailWord_150049) baseStart_150049 baseEnd_150049 := by
    simpa [prefixWord, tailWord_150049, baseEnd_150049] using wordTrace_append hprefix tailTrace_150049
  have hstable : (prefixWord ++ tailWord_150049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150049).length < 2 ^ (prefixWord ++ tailWord_150049).sum := by decide
  have hdescent : baseEnd_150049 < baseStart_150049 := by decide
  rcases family_descends (prefixWord ++ tailWord_150049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150089 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 5, 4, 3]
def baseStart_150089 : Nat := 118140960795 + 150089 * 2 ^ 59
def prefixEnd_150089 : Nat := 4983230072969 + 3 ^ 40 * 150089 * 2
def baseEnd_150089 : Nat := 77067797952768509797259

theorem tailTrace_150089 : CollatzResearch.WordTrace tailWord_150089 prefixEnd_150089 77067797952768509797259 := by
  unfold tailWord_150089
  simp only [CollatzResearch.WordTrace]
  refine ⟨5474195553260661005549321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3649463702173774003699547 5474195553260661005549321)
  ·
    refine ⟨4105646664945495754161991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5474195553260661005549321 4105646664945495754161991)
    ·
      refine ⟨6158469997418243631242987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4105646664945495754161991 6158469997418243631242987)
      ·
        refine ⟨9237704996127365446864481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6158469997418243631242987 9237704996127365446864481)
        ·
          refine ⟨6928278747095524085148361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9237704996127365446864481 6928278747095524085148361)
          ·
            refine ⟨5196209060321643063861271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6928278747095524085148361 5196209060321643063861271)
            ·
              refine ⟨7794313590482464595791907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5196209060321643063861271 7794313590482464595791907)
              ·
                refine ⟨11691470385723696893687861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7794313590482464595791907 11691470385723696893687861)
                ·
                  refine ⟨1096075348661596583783237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11691470385723696893687861 1096075348661596583783237)
                  ·
                    refine ⟨205514127874049359459357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1096075348661596583783237 205514127874049359459357)
                    ·
                      refine ⟨77067797952768509797259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 205514127874049359459357 77067797952768509797259)
                      ·
                        rfl

theorem cell23_150089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 4, 3].length) (baseStart_150089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_150089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_150089 prefixEnd_150089 := by exact prefixLift 150089
  have htrace : WordTrace (prefixWord ++ tailWord_150089) baseStart_150089 baseEnd_150089 := by
    simpa [prefixWord, tailWord_150089, baseEnd_150089] using wordTrace_append hprefix tailTrace_150089
  have hstable : (prefixWord ++ tailWord_150089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150089).length < 2 ^ (prefixWord ++ tailWord_150089).sum := by decide
  have hdescent : baseEnd_150089 < baseStart_150089 := by decide
  rcases family_descends (prefixWord ++ tailWord_150089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150120 : List Nat := [2, 1, 4, 3, 2, 2, 1, 1, 2, 1, 4]
def baseStart_150120 : Nat := 118140960795 + 150120 * 2 ^ 59
def prefixEnd_150120 : Nat := 4983230072969 + 3 ^ 40 * 150120 * 2
def baseEnd_150120 : Nat := 77083715853057888509617

theorem tailTrace_150120 : CollatzResearch.WordTrace tailWord_150120 prefixEnd_150120 77083715853057888509617 := by
  unfold tailWord_150120
  simp only [CollatzResearch.WordTrace]
  refine ⟨2737663108074176649963907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3650217477432235533285209 2737663108074176649963907)
  ·
    refine ⟨4106494662111264974945861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2737663108074176649963907 4106494662111264974945861)
    ·
      refine ⟨769967749145862182802349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4106494662111264974945861 769967749145862182802349)
      ·
        refine ⟨288737905929698318550881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 769967749145862182802349 288737905929698318550881)
        ·
          refine ⟨216553429447273738913161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 288737905929698318550881 216553429447273738913161)
          ·
            refine ⟨162415072085455304184871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216553429447273738913161 162415072085455304184871)
            ·
              refine ⟨243622608128182956277307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162415072085455304184871 243622608128182956277307)
              ·
                refine ⟨365433912192274434415961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 243622608128182956277307 365433912192274434415961)
                ·
                  refine ⟨274075434144205825811971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 365433912192274434415961 274075434144205825811971)
                  ·
                    refine ⟨411113151216308738717957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 274075434144205825811971 411113151216308738717957)
                    ·
                      refine ⟨77083715853057888509617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 411113151216308738717957 77083715853057888509617)
                      ·
                        rfl

theorem cell23_150120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_150120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_150120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_150120 prefixEnd_150120 := by exact prefixLift 150120
  have htrace : WordTrace (prefixWord ++ tailWord_150120) baseStart_150120 baseEnd_150120 := by
    simpa [prefixWord, tailWord_150120, baseEnd_150120] using wordTrace_append hprefix tailTrace_150120
  have hstable : (prefixWord ++ tailWord_150120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150120).length < 2 ^ (prefixWord ++ tailWord_150120).sum := by decide
  have hdescent : baseEnd_150120 < baseStart_150120 := by decide
  rcases family_descends (prefixWord ++ tailWord_150120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150139 : List Nat := [1, 1, 1, 1, 1, 4, 2, 2, 5, 5]
def baseStart_150139 : Nat := 118140960795 + 150139 * 2 ^ 59
def prefixEnd_150139 : Nat := 4983230072969 + 3 ^ 40 * 150139 * 2
def baseEnd_150139 : Nat := 25697823995164438057343

theorem tailTrace_150139 : CollatzResearch.WordTrace tailWord_150139 prefixEnd_150139 25697823995164438057343 := by
  unfold tailWord_150139
  simp only [CollatzResearch.WordTrace]
  refine ⟨5476019203079519544869471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3650679468719679696579647 5476019203079519544869471)
  ·
    refine ⟨8214028804619279317304207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5476019203079519544869471 8214028804619279317304207)
    ·
      refine ⟨12321043206928918975956311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8214028804619279317304207 12321043206928918975956311)
      ·
        refine ⟨18481564810393378463934467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12321043206928918975956311 18481564810393378463934467)
        ·
          refine ⟨27722347215590067695901701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18481564810393378463934467 27722347215590067695901701)
          ·
            refine ⟨5197940102923137692981569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27722347215590067695901701 5197940102923137692981569)
            ·
              refine ⟨3898455077192353269736177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5197940102923137692981569 3898455077192353269736177)
              ·
                refine ⟨2923841307894264952302133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3898455077192353269736177 2923841307894264952302133)
                ·
                  refine ⟨274110122615087339278325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2923841307894264952302133 274110122615087339278325)
                  ·
                    refine ⟨25697823995164438057343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 274110122615087339278325 25697823995164438057343)
                    ·
                      rfl

theorem cell23_150139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 5, 5].length) (baseStart_150139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_150139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_150139 prefixEnd_150139 := by exact prefixLift 150139
  have htrace : WordTrace (prefixWord ++ tailWord_150139) baseStart_150139 baseEnd_150139 := by
    simpa [prefixWord, tailWord_150139, baseEnd_150139] using wordTrace_append hprefix tailTrace_150139
  have hstable : (prefixWord ++ tailWord_150139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150139).length < 2 ^ (prefixWord ++ tailWord_150139).sum := by decide
  have hdescent : baseEnd_150139 < baseStart_150139 := by decide
  rcases family_descends (prefixWord ++ tailWord_150139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150190 : List Nat := [4, 1, 4, 1, 1, 1, 2, 3, 1, 5]
def baseStart_150190 : Nat := 118140960795 + 150190 * 2 ^ 59
def prefixEnd_150190 : Nat := 4983230072969 + 3 ^ 40 * 150190 * 2
def baseEnd_150190 : Nat := 25706553166290871544765

theorem tailTrace_150190 : CollatzResearch.WordTrace tailWord_150190 prefixEnd_150190 25706553166290871544765 := by
  unfold tailWord_150190
  simp only [CollatzResearch.WordTrace]
  refine ⟨684734915736844406872003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3651919550596503503317349 684734915736844406872003)
  ·
    refine ⟨1027102373605266610308005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 684734915736844406872003 1027102373605266610308005)
    ·
      refine ⟨192581695050987489432751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1027102373605266610308005 192581695050987489432751)
      ·
        refine ⟨288872542576481234149127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192581695050987489432751 288872542576481234149127)
        ·
          refine ⟨433308813864721851223691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288872542576481234149127 433308813864721851223691)
          ·
            refine ⟨649963220797082776835537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 433308813864721851223691 649963220797082776835537)
            ·
              refine ⟨487472415597812082626653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 649963220797082776835537 487472415597812082626653)
              ·
                refine ⟨182802155849179530984995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 487472415597812082626653 182802155849179530984995)
                ·
                  refine ⟨274203233773769296477493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 182802155849179530984995 274203233773769296477493)
                  ·
                    refine ⟨25706553166290871544765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 274203233773769296477493 25706553166290871544765)
                    ·
                      rfl

theorem cell23_150190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_150190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_150190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_150190 prefixEnd_150190 := by exact prefixLift 150190
  have htrace : WordTrace (prefixWord ++ tailWord_150190) baseStart_150190 baseEnd_150190 := by
    simpa [prefixWord, tailWord_150190, baseEnd_150190] using wordTrace_append hprefix tailTrace_150190
  have hstable : (prefixWord ++ tailWord_150190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150190).length < 2 ^ (prefixWord ++ tailWord_150190).sum := by decide
  have hdescent : baseEnd_150190 < baseStart_150190 := by decide
  rcases family_descends (prefixWord ++ tailWord_150190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150206 : List Nat := [4, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6]
def baseStart_150206 : Nat := 118140960795 + 150206 * 2 ^ 59
def prefixEnd_150206 : Nat := 4983230072969 + 3 ^ 40 * 150206 * 2
def baseEnd_150206 : Nat := 77127875189344552034221

theorem tailTrace_150206 : CollatzResearch.WordTrace tailWord_150206 prefixEnd_150206 77127875189344552034221 := by
  unfold tailWord_150206
  simp only [CollatzResearch.WordTrace]
  refine ⟨684807861729598748444809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3652308595891193325038981 684807861729598748444809)
  ·
    refine ⟨513605896297199061333607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 684807861729598748444809 513605896297199061333607)
    ·
      refine ⟨770408844445798592000411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 513605896297199061333607 770408844445798592000411)
      ·
        refine ⟨1155613266668697888000617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 770408844445798592000411 1155613266668697888000617)
        ·
          refine ⟨866709950001523416000463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1155613266668697888000617 866709950001523416000463)
          ·
            refine ⟨1300064925002285124000695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 866709950001523416000463 1300064925002285124000695)
            ·
              refine ⟨1950097387503427686001043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1300064925002285124000695 1950097387503427686001043)
              ·
                refine ⟨2925146081255141529001565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1950097387503427686001043 2925146081255141529001565)
                ·
                  refine ⟨1096929780470678073375587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2925146081255141529001565 1096929780470678073375587)
                  ·
                    refine ⟨1645394670706017110063381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1096929780470678073375587 1645394670706017110063381)
                    ·
                      refine ⟨77127875189344552034221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1645394670706017110063381 77127875189344552034221)
                      ·
                        rfl

theorem cell23_150206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_150206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_150206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_150206 prefixEnd_150206 := by exact prefixLift 150206
  have htrace : WordTrace (prefixWord ++ tailWord_150206) baseStart_150206 baseEnd_150206 := by
    simpa [prefixWord, tailWord_150206, baseEnd_150206] using wordTrace_append hprefix tailTrace_150206
  have hstable : (prefixWord ++ tailWord_150206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150206).length < 2 ^ (prefixWord ++ tailWord_150206).sum := by decide
  have hdescent : baseEnd_150206 < baseStart_150206 := by decide
  rcases family_descends (prefixWord ++ tailWord_150206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150216 : List Nat := [2, 1, 3, 1, 2, 4, 2, 8]
def baseStart_150216 : Nat := 118140960795 + 150216 * 2 ^ 59
def prefixEnd_150216 : Nat := 4983230072969 + 3 ^ 40 * 150216 * 2
def baseEnd_150216 : Nat := 2856778147995907885525

theorem tailTrace_150216 : CollatzResearch.WordTrace tailWord_150216 prefixEnd_150216 2856778147995907885525 := by
  unfold tailWord_150216
  simp only [CollatzResearch.WordTrace]
  refine ⟨2739413811900280847711251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3652551749200374463615001 2739413811900280847711251)
  ·
    refine ⟨4109120717850421271566877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2739413811900280847711251 4109120717850421271566877)
    ·
      refine ⟨1540920269193907976837579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4109120717850421271566877 1540920269193907976837579)
      ·
        refine ⟨2311380403790861965256369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1540920269193907976837579 2311380403790861965256369)
        ·
          refine ⟨1733535302843146473942277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2311380403790861965256369 1733535302843146473942277)
          ·
            refine ⟨325037869283089963864177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1733535302843146473942277 325037869283089963864177)
            ·
              refine ⟨243778401962317472898133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 325037869283089963864177 243778401962317472898133)
              ·
                refine ⟨2856778147995907885525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 243778401962317472898133 2856778147995907885525)
                ·
                  rfl

theorem cell23_150216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 8].length) (baseStart_150216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_150216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_150216 prefixEnd_150216 := by exact prefixLift 150216
  have htrace : WordTrace (prefixWord ++ tailWord_150216) baseStart_150216 baseEnd_150216 := by
    simpa [prefixWord, tailWord_150216, baseEnd_150216] using wordTrace_append hprefix tailTrace_150216
  have hstable : (prefixWord ++ tailWord_150216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150216).length < 2 ^ (prefixWord ++ tailWord_150216).sum := by decide
  have hdescent : baseEnd_150216 < baseStart_150216 := by decide
  rcases family_descends (prefixWord ++ tailWord_150216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150220 : List Nat := [2, 2, 1, 5, 1, 2, 1, 3, 2, 4]
def baseStart_150220 : Nat := 118140960795 + 150220 * 2 ^ 59
def prefixEnd_150220 : Nat := 4983230072969 + 3 ^ 40 * 150220 * 2
def baseEnd_150220 : Nat := 25711687972835832419719

theorem tailTrace_150220 : CollatzResearch.WordTrace tailWord_150220 prefixEnd_150220 25711687972835832419719 := by
  unfold tailWord_150220
  simp only [CollatzResearch.WordTrace]
  refine ⟨2739486757893035189284057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3652649010524046919045409 2739486757893035189284057)
  ·
    refine ⟨2054615068419776391963043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2739486757893035189284057 2054615068419776391963043)
    ·
      refine ⟨3081922602629664587944565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2054615068419776391963043 3081922602629664587944565)
      ·
        refine ⟨288930243996531055119803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3081922602629664587944565 288930243996531055119803)
        ·
          refine ⟨433395365994796582679705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288930243996531055119803 433395365994796582679705)
          ·
            refine ⟨325046524496097437009779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 433395365994796582679705 325046524496097437009779)
            ·
              refine ⟨487569786744146155514669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 325046524496097437009779 487569786744146155514669)
              ·
                refine ⟨182838670029054808318001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 487569786744146155514669 182838670029054808318001)
                ·
                  refine ⟨137129002521791106238501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 182838670029054808318001 137129002521791106238501)
                  ·
                    refine ⟨25711687972835832419719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 137129002521791106238501 25711687972835832419719)
                    ·
                      rfl

theorem cell23_150220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 3, 2, 4].length) (baseStart_150220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_150220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_150220 prefixEnd_150220 := by exact prefixLift 150220
  have htrace : WordTrace (prefixWord ++ tailWord_150220) baseStart_150220 baseEnd_150220 := by
    simpa [prefixWord, tailWord_150220, baseEnd_150220] using wordTrace_append hprefix tailTrace_150220
  have hstable : (prefixWord ++ tailWord_150220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150220).length < 2 ^ (prefixWord ++ tailWord_150220).sum := by decide
  have hdescent : baseEnd_150220 < baseStart_150220 := by decide
  rcases family_descends (prefixWord ++ tailWord_150220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150243 : List Nat := [1, 1, 1, 7, 1, 1, 1, 1, 3, 3, 3]
def baseStart_150243 : Nat := 118140960795 + 150243 * 2 ^ 59
def prefixEnd_150243 : Nat := 4983230072969 + 3 ^ 40 * 150243 * 2
def baseEnd_150243 : Nat := 77146873973560907271551

theorem tailTrace_150243 : CollatzResearch.WordTrace tailWord_150243 prefixEnd_150243 77146873973560907271551 := by
  unfold tailWord_150243
  simp only [CollatzResearch.WordTrace]
  refine ⟨5479812394702745306655383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3653208263135163537770255 5479812394702745306655383)
  ·
    refine ⟨8219718592054117959983075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5479812394702745306655383 8219718592054117959983075)
    ·
      refine ⟨12329577888081176939974613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8219718592054117959983075 12329577888081176939974613)
      ·
        refine ⟨288974481751902584530655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 12329577888081176939974613 288974481751902584530655)
        ·
          refine ⟨433461722627853876795983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288974481751902584530655 433461722627853876795983)
          ·
            refine ⟨650192583941780815193975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 433461722627853876795983 650192583941780815193975)
            ·
              refine ⟨975288875912671222790963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 650192583941780815193975 975288875912671222790963)
              ·
                refine ⟨1462933313869006834186445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 975288875912671222790963 1462933313869006834186445)
                ·
                  refine ⟨548599992700877562819917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1462933313869006834186445 548599992700877562819917)
                  ·
                    refine ⟨205724997262829086057469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 548599992700877562819917 205724997262829086057469)
                    ·
                      refine ⟨77146873973560907271551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 205724997262829086057469 77146873973560907271551)
                      ·
                        rfl

theorem cell23_150243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_150243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_150243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_150243 prefixEnd_150243 := by exact prefixLift 150243
  have htrace : WordTrace (prefixWord ++ tailWord_150243) baseStart_150243 baseEnd_150243 := by
    simpa [prefixWord, tailWord_150243, baseEnd_150243] using wordTrace_append hprefix tailTrace_150243
  have hstable : (prefixWord ++ tailWord_150243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150243).length < 2 ^ (prefixWord ++ tailWord_150243).sum := by decide
  have hdescent : baseEnd_150243 < baseStart_150243 := by decide
  rcases family_descends (prefixWord ++ tailWord_150243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150266 : List Nat := [3, 1, 1, 1, 1, 3, 3, 1, 2, 3, 4]
def baseStart_150266 : Nat := 118140960795 + 150266 * 2 ^ 59
def prefixEnd_150266 : Nat := 4983230072969 + 3 ^ 40 * 150266 * 2
def baseEnd_150266 : Nat := 77158684028614317283945

theorem tailTrace_150266 : CollatzResearch.WordTrace tailWord_150266 prefixEnd_150266 77158684028614317283945 := by
  unfold tailWord_150266
  simp only [CollatzResearch.WordTrace]
  refine ⟨1370162818404855058685663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3653767515746280156495101 1370162818404855058685663)
  ·
    refine ⟨2055244227607282588028495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1370162818404855058685663 2055244227607282588028495)
    ·
      refine ⟨3082866341410923882042743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2055244227607282588028495 3082866341410923882042743)
      ·
        refine ⟨4624299512116385823064115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3082866341410923882042743 4624299512116385823064115)
        ·
          refine ⟨6936449268174578734596173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4624299512116385823064115 6936449268174578734596173)
          ·
            refine ⟨2601168475565467025473565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6936449268174578734596173 2601168475565467025473565)
            ·
              refine ⟨975438178337050134552587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2601168475565467025473565 975438178337050134552587)
              ·
                refine ⟨1463157267505575201828881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 975438178337050134552587 1463157267505575201828881)
                ·
                  refine ⟨1097367950629181401371661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1463157267505575201828881 1097367950629181401371661)
                  ·
                    refine ⟨411512981485943025514373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1097367950629181401371661 411512981485943025514373)
                    ·
                      refine ⟨77158684028614317283945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 411512981485943025514373 77158684028614317283945)
                      ·
                        rfl

theorem cell23_150266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 2, 3, 4].length) (baseStart_150266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_150266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_150266 prefixEnd_150266 := by exact prefixLift 150266
  have htrace : WordTrace (prefixWord ++ tailWord_150266) baseStart_150266 baseEnd_150266 := by
    simpa [prefixWord, tailWord_150266, baseEnd_150266] using wordTrace_append hprefix tailTrace_150266
  have hstable : (prefixWord ++ tailWord_150266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150266).length < 2 ^ (prefixWord ++ tailWord_150266).sum := by decide
  have hdescent : baseEnd_150266 < baseStart_150266 := by decide
  rcases family_descends (prefixWord ++ tailWord_150266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150296 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 3, 4, 4]
def baseStart_150296 : Nat := 118140960795 + 150296 * 2 ^ 59
def prefixEnd_150296 : Nat := 4983230072969 + 3 ^ 40 * 150296 * 2
def baseEnd_150296 : Nat := 77174088448249199908807

theorem tailTrace_150296 : CollatzResearch.WordTrace tailWord_150296 prefixEnd_150296 77174088448249199908807 := by
  unfold tailWord_150296
  simp only [CollatzResearch.WordTrace]
  refine ⟨2740872731755367679167371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3654496975673823572223161 2740872731755367679167371)
  ·
    refine ⟨4111309097633051518751057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2740872731755367679167371 4111309097633051518751057)
    ·
      refine ⟨3083481823224788639063293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4111309097633051518751057 3083481823224788639063293)
      ·
        refine ⟨1156305683709295739648735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3083481823224788639063293 1156305683709295739648735)
        ·
          refine ⟨1734458525563943609473103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1156305683709295739648735 1734458525563943609473103)
          ·
            refine ⟨2601687788345915414209655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1734458525563943609473103 2601687788345915414209655)
            ·
              refine ⟨3902531682518873121314483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2601687788345915414209655 3902531682518873121314483)
              ·
                refine ⟨5853797523778309681971725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3902531682518873121314483 5853797523778309681971725)
                ·
                  refine ⟨2195174071416866130739397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5853797523778309681971725 2195174071416866130739397)
                  ·
                    refine ⟨411595138390662399513637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2195174071416866130739397 411595138390662399513637)
                    ·
                      refine ⟨77174088448249199908807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 411595138390662399513637 77174088448249199908807)
                      ·
                        rfl

theorem cell23_150296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_150296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_150296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_150296 prefixEnd_150296 := by exact prefixLift 150296
  have htrace : WordTrace (prefixWord ++ tailWord_150296) baseStart_150296 baseEnd_150296 := by
    simpa [prefixWord, tailWord_150296, baseEnd_150296] using wordTrace_append hprefix tailTrace_150296
  have hstable : (prefixWord ++ tailWord_150296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150296).length < 2 ^ (prefixWord ++ tailWord_150296).sum := by decide
  have hdescent : baseEnd_150296 < baseStart_150296 := by decide
  rcases family_descends (prefixWord ++ tailWord_150296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150300 : List Nat := [2, 2, 3, 1, 1, 3, 2, 2, 1, 4, 2]
def baseStart_150300 : Nat := 118140960795 + 150300 * 2 ^ 59
def prefixEnd_150300 : Nat := 4983230072969 + 3 ^ 40 * 150300 * 2
def baseEnd_150300 : Nat := 77176142370867184258789

theorem tailTrace_150300 : CollatzResearch.WordTrace tailWord_150300 prefixEnd_150300 77176142370867184258789 := by
  unfold tailWord_150300
  simp only [CollatzResearch.WordTrace]
  refine ⟨2740945677748122020740177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3654594236997496027653569 2740945677748122020740177)
  ·
    refine ⟨2055709258311091515555133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2740945677748122020740177 2055709258311091515555133)
    ·
      refine ⟨770890971866659318333175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2055709258311091515555133 770890971866659318333175)
      ·
        refine ⟨1156336457799988977499763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 770890971866659318333175 1156336457799988977499763)
        ·
          refine ⟨1734504686699983466249645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1156336457799988977499763 1734504686699983466249645)
          ·
            refine ⟨650439257512493799843617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1734504686699983466249645 650439257512493799843617)
            ·
              refine ⟨487829443134370349882713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 650439257512493799843617 487829443134370349882713)
              ·
                refine ⟨365872082350777762412035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 487829443134370349882713 365872082350777762412035)
                ·
                  refine ⟨548808123526166643618053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 365872082350777762412035 548808123526166643618053)
                  ·
                    refine ⟨102901523161156245678385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 548808123526166643618053 102901523161156245678385)
                    ·
                      refine ⟨77176142370867184258789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 102901523161156245678385 77176142370867184258789)
                      ·
                        rfl

theorem cell23_150300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 1, 4, 2].length) (baseStart_150300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_150300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_150300 prefixEnd_150300 := by exact prefixLift 150300
  have htrace : WordTrace (prefixWord ++ tailWord_150300) baseStart_150300 baseEnd_150300 := by
    simpa [prefixWord, tailWord_150300, baseEnd_150300] using wordTrace_append hprefix tailTrace_150300
  have hstable : (prefixWord ++ tailWord_150300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150300).length < 2 ^ (prefixWord ++ tailWord_150300).sum := by decide
  have hdescent : baseEnd_150300 < baseStart_150300 := by decide
  rcases family_descends (prefixWord ++ tailWord_150300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150304 : List Nat := [2, 1, 1, 5, 1, 4, 2, 1, 1, 3, 2]
def baseStart_150304 : Nat := 118140960795 + 150304 * 2 ^ 59
def prefixEnd_150304 : Nat := 4983230072969 + 3 ^ 40 * 150304 * 2
def baseEnd_150304 : Nat := 77178196293485168608771

theorem tailTrace_150304 : CollatzResearch.WordTrace tailWord_150304 prefixEnd_150304 77178196293485168608771 := by
  unfold tailWord_150304
  simp only [CollatzResearch.WordTrace]
  refine ⟨2741018623740876362312983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3654691498321168483083977 2741018623740876362312983)
  ·
    refine ⟨4111527935611314543469475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2741018623740876362312983 4111527935611314543469475)
    ·
      refine ⟨6167291903416971815204213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4111527935611314543469475 6167291903416971815204213)
      ·
        refine ⟨578183615945341107675395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6167291903416971815204213 578183615945341107675395)
        ·
          refine ⟨867275423918011661513093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 578183615945341107675395 867275423918011661513093)
          ·
            refine ⟨162614141984627186533705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 867275423918011661513093 162614141984627186533705)
            ·
              refine ⟨121960606488470389900279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162614141984627186533705 121960606488470389900279)
              ·
                refine ⟨182940909732705584850419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121960606488470389900279 182940909732705584850419)
                ·
                  refine ⟨274411364599058377275629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 182940909732705584850419 274411364599058377275629)
                  ·
                    refine ⟨102904261724646891478361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 274411364599058377275629 102904261724646891478361)
                    ·
                      refine ⟨77178196293485168608771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 102904261724646891478361 77178196293485168608771)
                      ·
                        rfl

theorem cell23_150304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_150304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_150304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_150304 prefixEnd_150304 := by exact prefixLift 150304
  have htrace : WordTrace (prefixWord ++ tailWord_150304) baseStart_150304 baseEnd_150304 := by
    simpa [prefixWord, tailWord_150304, baseEnd_150304] using wordTrace_append hprefix tailTrace_150304
  have hstable : (prefixWord ++ tailWord_150304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150304).length < 2 ^ (prefixWord ++ tailWord_150304).sum := by decide
  have hdescent : baseEnd_150304 < baseStart_150304 := by decide
  rcases family_descends (prefixWord ++ tailWord_150304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150323 : List Nat := [1, 1, 1, 2, 6, 2, 2, 1, 7]
def baseStart_150323 : Nat := 118140960795 + 150323 * 2 ^ 59
def prefixEnd_150323 : Nat := 4983230072969 + 3 ^ 40 * 150323 * 2
def baseEnd_150323 : Nat := 8576439158435621585687

theorem tailTrace_150323 : CollatzResearch.WordTrace tailWord_150323 prefixEnd_150323 8576439158435621585687 := by
  unfold tailWord_150323
  simp only [CollatzResearch.WordTrace]
  refine ⟨5482730234412918969567623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3655153489608612646378415 5482730234412918969567623)
  ·
    refine ⟨8224095351619378454351435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5482730234412918969567623 8224095351619378454351435)
    ·
      refine ⟨12336143027429067681527153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8224095351619378454351435 12336143027429067681527153)
      ·
        refine ⟨9252107270571800761145365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12336143027429067681527153 9252107270571800761145365)
        ·
          refine ⟨433692528308053160678689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9252107270571800761145365 433692528308053160678689)
          ·
            refine ⟨325269396231039870509017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 433692528308053160678689 325269396231039870509017)
            ·
              refine ⟨243952047173279902881763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 325269396231039870509017 243952047173279902881763)
              ·
                refine ⟨365928070759919854322645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 243952047173279902881763 365928070759919854322645)
                ·
                  refine ⟨8576439158435621585687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 365928070759919854322645 8576439158435621585687)
                  ·
                    rfl

theorem cell23_150323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 7].length) (baseStart_150323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_150323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_150323 prefixEnd_150323 := by exact prefixLift 150323
  have htrace : WordTrace (prefixWord ++ tailWord_150323) baseStart_150323 baseEnd_150323 := by
    simpa [prefixWord, tailWord_150323, baseEnd_150323] using wordTrace_append hprefix tailTrace_150323
  have hstable : (prefixWord ++ tailWord_150323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150323).length < 2 ^ (prefixWord ++ tailWord_150323).sum := by decide
  have hdescent : baseEnd_150323 < baseStart_150323 := by decide
  rcases family_descends (prefixWord ++ tailWord_150323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150334 : List Nat := [4, 2, 1, 2, 3, 2, 1, 1, 1, 4, 2]
def baseStart_150334 : Nat := 118140960795 + 150334 * 2 ^ 59
def prefixEnd_150334 : Nat := 4983230072969 + 3 ^ 40 * 150334 * 2
def baseEnd_150334 : Nat := 77193600713120051233633

theorem tailTrace_150334 : CollatzResearch.WordTrace tailWord_150334 prefixEnd_150334 77193600713120051233633 := by
  unfold tailWord_150334
  simp only [CollatzResearch.WordTrace]
  refine ⟨685391429671633481027257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3655420958248711898812037 685391429671633481027257)
  ·
    refine ⟨514043572253725110770443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 685391429671633481027257 514043572253725110770443)
    ·
      refine ⟨771065358380587666155665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 514043572253725110770443 771065358380587666155665)
      ·
        refine ⟨578299018785440749616749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 771065358380587666155665 578299018785440749616749)
        ·
          refine ⟨216862132044540281106281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 578299018785440749616749 216862132044540281106281)
          ·
            refine ⟨162646599033405210829711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216862132044540281106281 162646599033405210829711)
            ·
              refine ⟨243969898550107816244567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162646599033405210829711 243969898550107816244567)
              ·
                refine ⟨365954847825161724366851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 243969898550107816244567 365954847825161724366851)
                ·
                  refine ⟨548932271737742586550277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 365954847825161724366851 548932271737742586550277)
                  ·
                    refine ⟨102924800950826734978177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 548932271737742586550277 102924800950826734978177)
                    ·
                      refine ⟨77193600713120051233633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 102924800950826734978177 77193600713120051233633)
                      ·
                        rfl

theorem cell23_150334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_150334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_150334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_150334 prefixEnd_150334 := by exact prefixLift 150334
  have htrace : WordTrace (prefixWord ++ tailWord_150334) baseStart_150334 baseEnd_150334 := by
    simpa [prefixWord, tailWord_150334, baseEnd_150334] using wordTrace_append hprefix tailTrace_150334
  have hstable : (prefixWord ++ tailWord_150334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150334).length < 2 ^ (prefixWord ++ tailWord_150334).sum := by decide
  have hdescent : baseEnd_150334 < baseStart_150334 := by decide
  rcases family_descends (prefixWord ++ tailWord_150334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150346 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 3, 1, 7]
def baseStart_150346 : Nat := 118140960795 + 150346 * 2 ^ 59
def prefixEnd_150346 : Nat := 4983230072969 + 3 ^ 40 * 150346 * 2
def baseEnd_150346 : Nat := 77199762480974004283577

theorem tailTrace_150346 : CollatzResearch.WordTrace tailWord_150346 prefixEnd_150346 77199762480974004283577 := by
  unfold tailWord_150346
  simp only [CollatzResearch.WordTrace]
  refine ⟨1370892278332398474413723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3655712742219729265103261 1370892278332398474413723)
  ·
    refine ⟨2056338417498597711620585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1370892278332398474413723 2056338417498597711620585)
    ·
      refine ⟨1542253813123948283715439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2056338417498597711620585 1542253813123948283715439)
      ·
        refine ⟨2313380719685922425573159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1542253813123948283715439 2313380719685922425573159)
        ·
          refine ⟨3470071079528883638359739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2313380719685922425573159 3470071079528883638359739)
          ·
            refine ⟨5205106619293325457539609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3470071079528883638359739 5205106619293325457539609)
            ·
              refine ⟨3903829964469994093154707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5205106619293325457539609 3903829964469994093154707)
              ·
                refine ⟨5855744946704991139732061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3903829964469994093154707 5855744946704991139732061)
                ·
                  refine ⟨2195904355014371677399523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5855744946704991139732061 2195904355014371677399523)
                  ·
                    refine ⟨3293856532521557516099285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2195904355014371677399523 3293856532521557516099285)
                    ·
                      refine ⟨77199762480974004283577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 3293856532521557516099285 77199762480974004283577)
                      ·
                        rfl

theorem cell23_150346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_150346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_150346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_150346 prefixEnd_150346 := by exact prefixLift 150346
  have htrace : WordTrace (prefixWord ++ tailWord_150346) baseStart_150346 baseEnd_150346 := by
    simpa [prefixWord, tailWord_150346, baseEnd_150346] using wordTrace_append hprefix tailTrace_150346
  have hstable : (prefixWord ++ tailWord_150346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150346).length < 2 ^ (prefixWord ++ tailWord_150346).sum := by decide
  have hdescent : baseEnd_150346 < baseStart_150346 := by decide
  rcases family_descends (prefixWord ++ tailWord_150346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150373 : List Nat := [1, 3, 1, 3, 1, 1, 3, 1, 4, 1, 4]
def baseStart_150373 : Nat := 118140960795 + 150373 * 2 ^ 59
def prefixEnd_150373 : Nat := 4983230072969 + 3 ^ 40 * 150373 * 2
def baseEnd_150373 : Nat := 77213626458645398645953

theorem tailTrace_150373 : CollatzResearch.WordTrace tailWord_150373 prefixEnd_150373 77213626458645398645953 := by
  unfold tailWord_150373
  simp only [CollatzResearch.WordTrace]
  refine ⟨5484553884231777508887773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3656369256154518339258515 5484553884231777508887773)
  ·
    refine ⟨2056707706586916565832915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5484553884231777508887773 2056707706586916565832915)
    ·
      refine ⟨3085061559880374848749373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2056707706586916565832915 3085061559880374848749373)
      ·
        refine ⟨1156898084955140568281015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3085061559880374848749373 1156898084955140568281015)
        ·
          refine ⟨1735347127432710852421523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1156898084955140568281015 1735347127432710852421523)
          ·
            refine ⟨2603020691149066278632285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1735347127432710852421523 2603020691149066278632285)
            ·
              refine ⟨976132759180899854487107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2603020691149066278632285 976132759180899854487107)
              ·
                refine ⟨1464199138771349781730661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 976132759180899854487107 1464199138771349781730661)
                ·
                  refine ⟨274537338519628084074499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1464199138771349781730661 274537338519628084074499)
                  ·
                    refine ⟨411806007779442126111749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 274537338519628084074499 411806007779442126111749)
                    ·
                      refine ⟨77213626458645398645953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 411806007779442126111749 77213626458645398645953)
                      ·
                        rfl

theorem cell23_150373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_150373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_150373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_150373 prefixEnd_150373 := by exact prefixLift 150373
  have htrace : WordTrace (prefixWord ++ tailWord_150373) baseStart_150373 baseEnd_150373 := by
    simpa [prefixWord, tailWord_150373, baseEnd_150373] using wordTrace_append hprefix tailTrace_150373
  have hstable : (prefixWord ++ tailWord_150373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150373).length < 2 ^ (prefixWord ++ tailWord_150373).sum := by decide
  have hdescent : baseEnd_150373 < baseStart_150373 := by decide
  rcases family_descends (prefixWord ++ tailWord_150373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150434 : List Nat := [3, 3, 1, 2, 2, 2, 1, 4, 1, 4]
def baseStart_150434 : Nat := 118140960795 + 150434 * 2 ^ 59
def prefixEnd_150434 : Nat := 4983230072969 + 3 ^ 40 * 150434 * 2
def baseEnd_150434 : Nat := 25748316259523219994391

theorem tailTrace_150434 : CollatzResearch.WordTrace tailWord_150434 prefixEnd_150434 25748316259523219994391 := by
  unfold tailWord_150434
  simp only [CollatzResearch.WordTrace]
  refine ⟨1371694684252696231714589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3657852491340523284572237 1371694684252696231714589)
  ·
    refine ⟨514385506594761086892971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1371694684252696231714589 514385506594761086892971)
    ·
      refine ⟨771578259892141630339457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 514385506594761086892971 771578259892141630339457)
      ·
        refine ⟨578683694919106222754593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 771578259892141630339457 578683694919106222754593)
        ·
          refine ⟨434012771189329667065945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 578683694919106222754593 434012771189329667065945)
          ·
            refine ⟨325509578391997250299459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 434012771189329667065945 325509578391997250299459)
            ·
              refine ⟨488264367587995875449189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 325509578391997250299459 488264367587995875449189)
              ·
                refine ⟨91549568922749226646723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 488264367587995875449189 91549568922749226646723)
                ·
                  refine ⟨137324353384123839970085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91549568922749226646723 137324353384123839970085)
                  ·
                    refine ⟨25748316259523219994391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 137324353384123839970085 25748316259523219994391)
                    ·
                      rfl

theorem cell23_150434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_150434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_150434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_150434 prefixEnd_150434 := by exact prefixLift 150434
  have htrace : WordTrace (prefixWord ++ tailWord_150434) baseStart_150434 baseEnd_150434 := by
    simpa [prefixWord, tailWord_150434, baseEnd_150434] using wordTrace_append hprefix tailTrace_150434
  have hstable : (prefixWord ++ tailWord_150434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150434).length < 2 ^ (prefixWord ++ tailWord_150434).sum := by decide
  have hdescent : baseEnd_150434 < baseStart_150434 := by decide
  rcases family_descends (prefixWord ++ tailWord_150434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150453 : List Nat := [1, 3, 3, 2, 1, 1, 1, 1, 2, 1, 7]
def baseStart_150453 : Nat := 118140960795 + 150453 * 2 ^ 59
def prefixEnd_150453 : Nat := 4983230072969 + 3 ^ 40 * 150453 * 2
def baseEnd_150453 : Nat := 77254704911005085645585

theorem tailTrace_150453 : CollatzResearch.WordTrace tailWord_150453 prefixEnd_150453 77254704911005085645585 := by
  unfold tailWord_150453
  simp only [CollatzResearch.WordTrace]
  refine ⟨5487471723941951171800013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3658314482627967447866675 5487471723941951171800013)
  ·
    refine ⟨2057801896478231689425005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5487471723941951171800013 2057801896478231689425005)
    ·
      refine ⟨771675711179336883534377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2057801896478231689425005 771675711179336883534377)
      ·
        refine ⟨578756783384502662650783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 771675711179336883534377 578756783384502662650783)
        ·
          refine ⟨868135175076753993976175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 578756783384502662650783 868135175076753993976175)
          ·
            refine ⟨1302202762615130990964263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 868135175076753993976175 1302202762615130990964263)
            ·
              refine ⟨1953304143922696486446395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1302202762615130990964263 1953304143922696486446395)
              ·
                refine ⟨2929956215884044729669593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1953304143922696486446395 2929956215884044729669593)
                ·
                  refine ⟨2197467161913033547252195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2929956215884044729669593 2197467161913033547252195)
                  ·
                    refine ⟨3296200742869550320878293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2197467161913033547252195 3296200742869550320878293)
                    ·
                      refine ⟨77254704911005085645585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 3296200742869550320878293 77254704911005085645585)
                      ·
                        rfl

theorem cell23_150453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_150453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_150453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_150453 prefixEnd_150453 := by exact prefixLift 150453
  have htrace : WordTrace (prefixWord ++ tailWord_150453) baseStart_150453 baseEnd_150453 := by
    simpa [prefixWord, tailWord_150453, baseEnd_150453] using wordTrace_append hprefix tailTrace_150453
  have hstable : (prefixWord ++ tailWord_150453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150453).length < 2 ^ (prefixWord ++ tailWord_150453).sum := by decide
  have hdescent : baseEnd_150453 < baseStart_150453 := by decide
  rcases family_descends (prefixWord ++ tailWord_150453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150457 : List Nat := [1, 2, 1, 4, 2, 3, 1, 2, 3, 1, 3]
def baseStart_150457 : Nat := 118140960795 + 150457 * 2 ^ 59
def prefixEnd_150457 : Nat := 4983230072969 + 3 ^ 40 * 150457 * 2
def baseEnd_150457 : Nat := 77256758833623069995567

theorem tailTrace_150457 : CollatzResearch.WordTrace tailWord_150457 prefixEnd_150457 77256758833623069995567 := by
  unfold tailWord_150457
  simp only [CollatzResearch.WordTrace]
  refine ⟨5487617615927459854945625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3658411743951639903297083 5487617615927459854945625)
  ·
    refine ⟨4115713211945594891209219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5487617615927459854945625 4115713211945594891209219)
    ·
      refine ⟨6173569817918392336813829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4115713211945594891209219 6173569817918392336813829)
      ·
        refine ⟨1157544340859698563152593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6173569817918392336813829 1157544340859698563152593)
        ·
          refine ⟨868158255644773922364445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1157544340859698563152593 868158255644773922364445)
          ·
            refine ⟨325559345866790220886667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 868158255644773922364445 325559345866790220886667)
            ·
              refine ⟨488339018800185331330001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 325559345866790220886667 488339018800185331330001)
              ·
                refine ⟨366254264100138998497501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 488339018800185331330001 366254264100138998497501)
                ·
                  refine ⟨137345349037552124436563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 366254264100138998497501 137345349037552124436563)
                  ·
                    refine ⟨206018023556328186654845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 137345349037552124436563 206018023556328186654845)
                    ·
                      refine ⟨77256758833623069995567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 206018023556328186654845 77256758833623069995567)
                      ·
                        rfl

theorem cell23_150457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_150457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_150457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_150457 prefixEnd_150457 := by exact prefixLift 150457
  have htrace : WordTrace (prefixWord ++ tailWord_150457) baseStart_150457 baseEnd_150457 := by
    simpa [prefixWord, tailWord_150457, baseEnd_150457] using wordTrace_append hprefix tailTrace_150457
  have hstable : (prefixWord ++ tailWord_150457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150457).length < 2 ^ (prefixWord ++ tailWord_150457).sum := by decide
  have hdescent : baseEnd_150457 < baseStart_150457 := by decide
  rcases family_descends (prefixWord ++ tailWord_150457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150500 : List Nat := [2, 3, 1, 1, 1, 1, 2, 4, 3, 2, 3]
def baseStart_150500 : Nat := 118140960795 + 150500 * 2 ^ 59
def prefixEnd_150500 : Nat := 4983230072969 + 3 ^ 40 * 150500 * 2
def baseEnd_150500 : Nat := 77278838501766401757869

theorem tailTrace_150500 : CollatzResearch.WordTrace tailWord_150500 prefixEnd_150500 77278838501766401757869 := by
  unfold tailWord_150500
  simp only [CollatzResearch.WordTrace]
  refine ⟨2744592977385839099380477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3659457303181118799173969 2744592977385839099380477)
  ·
    refine ⟨1029222366519689662267679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2744592977385839099380477 1029222366519689662267679)
    ·
      refine ⟨1543833549779534493401519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1029222366519689662267679 1543833549779534493401519)
      ·
        refine ⟨2315750324669301740102279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1543833549779534493401519 2315750324669301740102279)
        ·
          refine ⟨3473625487003952610153419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2315750324669301740102279 3473625487003952610153419)
          ·
            refine ⟨5210438230505928915230129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3473625487003952610153419 5210438230505928915230129)
            ·
              refine ⟨3907828672879446686422597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5210438230505928915230129 3907828672879446686422597)
              ·
                refine ⟨732717876164896253704237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3907828672879446686422597 732717876164896253704237)
                ·
                  refine ⟨274769203561836095139089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 732717876164896253704237 274769203561836095139089)
                  ·
                    refine ⟨206076902671377071354317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 274769203561836095139089 206076902671377071354317)
                    ·
                      refine ⟨77278838501766401757869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 206076902671377071354317 77278838501766401757869)
                      ·
                        rfl

theorem cell23_150500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 3, 2, 3].length) (baseStart_150500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_150500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_150500 prefixEnd_150500 := by exact prefixLift 150500
  have htrace : WordTrace (prefixWord ++ tailWord_150500) baseStart_150500 baseEnd_150500 := by
    simpa [prefixWord, tailWord_150500, baseEnd_150500] using wordTrace_append hprefix tailTrace_150500
  have hstable : (prefixWord ++ tailWord_150500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150500).length < 2 ^ (prefixWord ++ tailWord_150500).sum := by decide
  have hdescent : baseEnd_150500 < baseStart_150500 := by decide
  rcases family_descends (prefixWord ++ tailWord_150500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150547 : List Nat := [1, 1, 1, 2, 1, 4, 1, 6, 2, 1, 3]
def baseStart_150547 : Nat := 118140960795 + 150547 * 2 ^ 59
def prefixEnd_150547 : Nat := 4983230072969 + 3 ^ 40 * 150547 * 2
def baseEnd_150547 : Nat := 77302972092527717870153

theorem tailTrace_150547 : CollatzResearch.WordTrace tailWord_150547 prefixEnd_150547 77302972092527717870153 := by
  unfold tailWord_150547
  simp only [CollatzResearch.WordTrace]
  refine ⟨5490900185601405225721895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3660600123734270150481263 5490900185601405225721895)
  ·
    refine ⟨8236350278402107838582843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5490900185601405225721895 8236350278402107838582843)
    ·
      refine ⟨12354525417603161757874265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8236350278402107838582843 12354525417603161757874265)
      ·
        refine ⟨9265894063202371318405699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12354525417603161757874265 9265894063202371318405699)
        ·
          refine ⟨13898841094803556977608549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9265894063202371318405699 13898841094803556977608549)
          ·
            refine ⟨2606032705275666933301603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13898841094803556977608549 2606032705275666933301603)
            ·
              refine ⟨3909049057913500399952405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2606032705275666933301603 3909049057913500399952405)
              ·
                refine ⟨183236674589695331247769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3909049057913500399952405 183236674589695331247769)
                ·
                  refine ⟨137427505942271498435827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 183236674589695331247769 137427505942271498435827)
                  ·
                    refine ⟨206141258913407247653741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 137427505942271498435827 206141258913407247653741)
                    ·
                      refine ⟨77302972092527717870153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 206141258913407247653741 77302972092527717870153)
                      ·
                        rfl

theorem cell23_150547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 6, 2, 1, 3].length) (baseStart_150547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_150547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_150547 prefixEnd_150547 := by exact prefixLift 150547
  have htrace : WordTrace (prefixWord ++ tailWord_150547) baseStart_150547 baseEnd_150547 := by
    simpa [prefixWord, tailWord_150547, baseEnd_150547] using wordTrace_append hprefix tailTrace_150547
  have hstable : (prefixWord ++ tailWord_150547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150547).length < 2 ^ (prefixWord ++ tailWord_150547).sum := by decide
  have hdescent : baseEnd_150547 < baseStart_150547 := by decide
  rcases family_descends (prefixWord ++ tailWord_150547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150574 : List Nat := [4, 1, 3, 1, 1, 1, 3, 1, 3, 3, 2]
def baseStart_150574 : Nat := 118140960795 + 150574 * 2 ^ 59
def prefixEnd_150574 : Nat := 4983230072969 + 3 ^ 40 * 150574 * 2
def baseEnd_150574 : Nat := 77316836070199112232529

theorem tailTrace_150574 : CollatzResearch.WordTrace tailWord_150574 prefixEnd_150574 77316836070199112232529 := by
  unfold tailWord_150574
  simp only [CollatzResearch.WordTrace]
  refine ⟨686485619562948604619347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3661256637669059224636517 686485619562948604619347)
  ·
    refine ⟨1029728429344422906929021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 686485619562948604619347 1029728429344422906929021)
    ·
      refine ⟨386148161004158590098383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1029728429344422906929021 386148161004158590098383)
      ·
        refine ⟨579222241506237885147575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 386148161004158590098383 579222241506237885147575)
        ·
          refine ⟨868833362259356827721363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 579222241506237885147575 868833362259356827721363)
          ·
            refine ⟨1303250043389035241582045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 868833362259356827721363 1303250043389035241582045)
            ·
              refine ⟨488718766270888215593267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1303250043389035241582045 488718766270888215593267)
              ·
                refine ⟨733078149406332323389901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 488718766270888215593267 733078149406332323389901)
                ·
                  refine ⟨274904306027374621271213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 733078149406332323389901 274904306027374621271213)
                  ·
                    refine ⟨103089114760265482976705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 274904306027374621271213 103089114760265482976705)
                    ·
                      refine ⟨77316836070199112232529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 103089114760265482976705 77316836070199112232529)
                      ·
                        rfl

theorem cell23_150574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_150574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_150574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_150574 prefixEnd_150574 := by exact prefixLift 150574
  have htrace : WordTrace (prefixWord ++ tailWord_150574) baseStart_150574 baseEnd_150574 := by
    simpa [prefixWord, tailWord_150574, baseEnd_150574] using wordTrace_append hprefix tailTrace_150574
  have hstable : (prefixWord ++ tailWord_150574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150574).length < 2 ^ (prefixWord ++ tailWord_150574).sum := by decide
  have hdescent : baseEnd_150574 < baseStart_150574 := by decide
  rcases family_descends (prefixWord ++ tailWord_150574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150598 : List Nat := [6, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3]
def baseStart_150598 : Nat := 118140960795 + 150598 * 2 ^ 59
def prefixEnd_150598 : Nat := 4983230072969 + 3 ^ 40 * 150598 * 2
def baseEnd_150598 : Nat := 77329159605907018332419

theorem tailTrace_150598 : CollatzResearch.WordTrace tailWord_150598 prefixEnd_150598 77329159605907018332419 := by
  unfold tailWord_150598
  simp only [CollatzResearch.WordTrace]
  refine ⟨171648759638020029244639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3661840205611093957218965 171648759638020029244639)
  ·
    refine ⟨257473139457030043866959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171648759638020029244639 257473139457030043866959)
    ·
      refine ⟨386209709185545065800439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257473139457030043866959 386209709185545065800439)
      ·
        refine ⟨579314563778317598700659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 386209709185545065800439 579314563778317598700659)
        ·
          refine ⟨868971845667476398050989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 579314563778317598700659 868971845667476398050989)
          ·
            refine ⟨325864442125303649269121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 868971845667476398050989 325864442125303649269121)
            ·
              refine ⟨244398331593977736951841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 325864442125303649269121 244398331593977736951841)
              ·
                refine ⟨183298748695483302713881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 244398331593977736951841 183298748695483302713881)
                ·
                  refine ⟨137474061521612477035411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 183298748695483302713881 137474061521612477035411)
                  ·
                    refine ⟨206211092282418715553117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 137474061521612477035411 206211092282418715553117)
                    ·
                      refine ⟨77329159605907018332419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 206211092282418715553117 77329159605907018332419)
                      ·
                        rfl

theorem cell23_150598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_150598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_150598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_150598 prefixEnd_150598 := by exact prefixLift 150598
  have htrace : WordTrace (prefixWord ++ tailWord_150598) baseStart_150598 baseEnd_150598 := by
    simpa [prefixWord, tailWord_150598, baseEnd_150598] using wordTrace_append hprefix tailTrace_150598
  have hstable : (prefixWord ++ tailWord_150598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150598).length < 2 ^ (prefixWord ++ tailWord_150598).sum := by decide
  have hdescent : baseEnd_150598 < baseStart_150598 := by decide
  rcases family_descends (prefixWord ++ tailWord_150598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150600 : List Nat := [2, 1, 3, 1, 1, 1, 4, 2, 2, 2, 4]
def baseStart_150600 : Nat := 118140960795 + 150600 * 2 ^ 59
def prefixEnd_150600 : Nat := 4983230072969 + 3 ^ 40 * 150600 * 2
def baseEnd_150600 : Nat := 77330186567216010507409

theorem tailTrace_150600 : CollatzResearch.WordTrace tailWord_150600 prefixEnd_150600 77330186567216010507409 := by
  unfold tailWord_150600
  simp only [CollatzResearch.WordTrace]
  refine ⟨2746416627204697638700627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3661888836272930184934169 2746416627204697638700627)
  ·
    refine ⟨4119624940807046458050941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2746416627204697638700627 4119624940807046458050941)
    ·
      refine ⟨1544859352802642421769103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4119624940807046458050941 1544859352802642421769103)
      ·
        refine ⟨2317289029203963632653655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1544859352802642421769103 2317289029203963632653655)
        ·
          refine ⟨3475933543805945448980483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2317289029203963632653655 3475933543805945448980483)
          ·
            refine ⟨5213900315708918173470725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3475933543805945448980483 5213900315708918173470725)
            ·
              refine ⟨977606309195422157525761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5213900315708918173470725 977606309195422157525761)
              ·
                refine ⟨733204731896566618144321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 977606309195422157525761 733204731896566618144321)
                ·
                  refine ⟨549903548922424963608241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 733204731896566618144321 549903548922424963608241)
                  ·
                    refine ⟨412427661691818722706181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 549903548922424963608241 412427661691818722706181)
                    ·
                      refine ⟨77330186567216010507409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 412427661691818722706181 77330186567216010507409)
                      ·
                        rfl

theorem cell23_150600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_150600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_150600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_150600 prefixEnd_150600 := by exact prefixLift 150600
  have htrace : WordTrace (prefixWord ++ tailWord_150600) baseStart_150600 baseEnd_150600 := by
    simpa [prefixWord, tailWord_150600, baseEnd_150600] using wordTrace_append hprefix tailTrace_150600
  have hstable : (prefixWord ++ tailWord_150600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150600).length < 2 ^ (prefixWord ++ tailWord_150600).sum := by decide
  have hdescent : baseEnd_150600 < baseStart_150600 := by decide
  rcases family_descends (prefixWord ++ tailWord_150600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150640 : List Nat := [2, 1, 1, 1, 5, 1, 3, 1, 1, 7]
def baseStart_150640 : Nat := 118140960795 + 150640 * 2 ^ 59
def prefixEnd_150640 : Nat := 4983230072969 + 3 ^ 40 * 150640 * 2
def baseEnd_150640 : Nat := 25783575264465284669075

theorem tailTrace_150640 : CollatzResearch.WordTrace tailWord_150640 prefixEnd_150640 25783575264465284669075 := by
  unfold tailWord_150640
  simp only [CollatzResearch.WordTrace]
  refine ⟨2747146087132241054428687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3662861449509654739238249 2747146087132241054428687)
  ·
    refine ⟨4120719130698361581643031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2747146087132241054428687 4120719130698361581643031)
    ·
      refine ⟨6181078696047542372464547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4120719130698361581643031 6181078696047542372464547)
      ·
        refine ⟨9271618044071313558696821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6181078696047542372464547 9271618044071313558696821)
        ·
          refine ⟨869214191631685646127827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9271618044071313558696821 869214191631685646127827)
          ·
            refine ⟨1303821287447528469191741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 869214191631685646127827 1303821287447528469191741)
            ·
              refine ⟨488932982792823175946903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1303821287447528469191741 488932982792823175946903)
              ·
                refine ⟨733399474189234763920355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 488932982792823175946903 733399474189234763920355)
                ·
                  refine ⟨1100099211283852145880533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 733399474189234763920355 1100099211283852145880533)
                  ·
                    refine ⟨25783575264465284669075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1100099211283852145880533 25783575264465284669075)
                    ·
                      rfl

theorem cell23_150640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 1, 7].length) (baseStart_150640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_150640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_150640 prefixEnd_150640 := by exact prefixLift 150640
  have htrace : WordTrace (prefixWord ++ tailWord_150640) baseStart_150640 baseEnd_150640 := by
    simpa [prefixWord, tailWord_150640, baseEnd_150640] using wordTrace_append hprefix tailTrace_150640
  have hstable : (prefixWord ++ tailWord_150640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150640).length < 2 ^ (prefixWord ++ tailWord_150640).sum := by decide
  have hdescent : baseEnd_150640 < baseStart_150640 := by decide
  rcases family_descends (prefixWord ++ tailWord_150640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150677 : List Nat := [1, 3, 2, 1, 1, 1, 2, 3, 1, 6, 2]
def baseStart_150677 : Nat := 118140960795 + 150677 * 2 ^ 59
def prefixEnd_150677 : Nat := 4983230072969 + 3 ^ 40 * 150677 * 2
def baseEnd_150677 : Nat := 77369724577612209244555

theorem tailTrace_150677 : CollatzResearch.WordTrace tailWord_150677 prefixEnd_150677 77369724577612209244555 := by
  unfold tailWord_150677
  simp only [CollatzResearch.WordTrace]
  refine ⟨5495641675130437427954285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3663761116753624951969523 5495641675130437427954285)
  ·
    refine ⟨2060865628173914035482857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5495641675130437427954285 2060865628173914035482857)
    ·
      refine ⟨1545649221130435526612143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2060865628173914035482857 1545649221130435526612143)
      ·
        refine ⟨2318473831695653289918215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1545649221130435526612143 2318473831695653289918215)
        ·
          refine ⟨3477710747543479934877323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2318473831695653289918215 3477710747543479934877323)
          ·
            refine ⟨5216566121315219902315985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3477710747543479934877323 5216566121315219902315985)
            ·
              refine ⟨3912424590986414926736989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5216566121315219902315985 3912424590986414926736989)
              ·
                refine ⟨1467159221619905597526371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3912424590986414926736989 1467159221619905597526371)
                ·
                  refine ⟨2200738832429858396289557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1467159221619905597526371 2200738832429858396289557)
                  ·
                    refine ⟨103159632770149612326073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2200738832429858396289557 103159632770149612326073)
                    ·
                      refine ⟨77369724577612209244555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 103159632770149612326073 77369724577612209244555)
                      ·
                        rfl

theorem cell23_150677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 6, 2].length) (baseStart_150677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_150677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_150677 prefixEnd_150677 := by exact prefixLift 150677
  have htrace : WordTrace (prefixWord ++ tailWord_150677) baseStart_150677 baseEnd_150677 := by
    simpa [prefixWord, tailWord_150677, baseEnd_150677] using wordTrace_append hprefix tailTrace_150677
  have hstable : (prefixWord ++ tailWord_150677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150677).length < 2 ^ (prefixWord ++ tailWord_150677).sum := by decide
  have hdescent : baseEnd_150677 < baseStart_150677 := by decide
  rcases family_descends (prefixWord ++ tailWord_150677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150721 : List Nat := [1, 2, 6, 1, 1, 1, 3, 1, 3, 4]
def baseStart_150721 : Nat := 118140960795 + 150721 * 2 ^ 59
def prefixEnd_150721 : Nat := 4983230072969 + 3 ^ 40 * 150721 * 2
def baseEnd_150721 : Nat := 25797439242136679031451

theorem tailTrace_150721 : CollatzResearch.WordTrace tailWord_150721 prefixEnd_150721 25797439242136679031451 := by
  unfold tailWord_150721
  simp only [CollatzResearch.WordTrace]
  refine ⟨5497246486971032942556017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3664830991314021961704011 5497246486971032942556017)
  ·
    refine ⟨4122934865228274706917013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5497246486971032942556017 4122934865228274706917013)
    ·
      refine ⟨193262571807575376886735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4122934865228274706917013 193262571807575376886735)
      ·
        refine ⟨289893857711363065330103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193262571807575376886735 289893857711363065330103)
        ·
          refine ⟨434840786567044597995155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289893857711363065330103 434840786567044597995155)
          ·
            refine ⟨652261179850566896992733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 434840786567044597995155 652261179850566896992733)
            ·
              refine ⟨244597942443962586372275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 652261179850566896992733 244597942443962586372275)
              ·
                refine ⟨366896913665943879558413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 244597942443962586372275 366896913665943879558413)
                ·
                  refine ⟨137586342624728954834405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 366896913665943879558413 137586342624728954834405)
                  ·
                    refine ⟨25797439242136679031451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 137586342624728954834405 25797439242136679031451)
                    ·
                      rfl

theorem cell23_150721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_150721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_150721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_150721 prefixEnd_150721 := by exact prefixLift 150721
  have htrace : WordTrace (prefixWord ++ tailWord_150721) baseStart_150721 baseEnd_150721 := by
    simpa [prefixWord, tailWord_150721, baseEnd_150721] using wordTrace_append hprefix tailTrace_150721
  have hstable : (prefixWord ++ tailWord_150721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150721).length < 2 ^ (prefixWord ++ tailWord_150721).sum := by decide
  have hdescent : baseEnd_150721 < baseStart_150721 := by decide
  rcases family_descends (prefixWord ++ tailWord_150721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150734 : List Nat := [4, 1, 1, 1, 5, 1, 1, 3, 6]
def baseStart_150734 : Nat := 118140960795 + 150734 * 2 ^ 59
def prefixEnd_150734 : Nat := 4983230072969 + 3 ^ 40 * 150734 * 2
def baseEnd_150734 : Nat := 8599888108324276247977

theorem tailTrace_150734 : CollatzResearch.WordTrace tailWord_150734 prefixEnd_150734 8599888108324276247977 := by
  unfold tailWord_150734
  simp only [CollatzResearch.WordTrace]
  refine ⟨687215079490492020347407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3665147090615957441852837 687215079490492020347407)
  ·
    refine ⟨1030822619235738030521111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 687215079490492020347407 1030822619235738030521111)
    ·
      refine ⟨1546233928853607045781667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1030822619235738030521111 1546233928853607045781667)
      ·
        refine ⟨2319350893280410568672501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1546233928853607045781667 2319350893280410568672501)
        ·
          refine ⟨217439146245038490813047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2319350893280410568672501 217439146245038490813047)
          ·
            refine ⟨326158719367557736219571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217439146245038490813047 326158719367557736219571)
            ·
              refine ⟨489238079051336604329357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 326158719367557736219571 489238079051336604329357)
              ·
                refine ⟨183464279644251226623509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 489238079051336604329357 183464279644251226623509)
                ·
                  refine ⟨8599888108324276247977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 183464279644251226623509 8599888108324276247977)
                  ·
                    rfl

theorem cell23_150734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 3, 6].length) (baseStart_150734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_150734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_150734 prefixEnd_150734 := by exact prefixLift 150734
  have htrace : WordTrace (prefixWord ++ tailWord_150734) baseStart_150734 baseEnd_150734 := by
    simpa [prefixWord, tailWord_150734, baseEnd_150734] using wordTrace_append hprefix tailTrace_150734
  have hstable : (prefixWord ++ tailWord_150734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150734).length < 2 ^ (prefixWord ++ tailWord_150734).sum := by decide
  have hdescent : baseEnd_150734 < baseStart_150734 := by decide
  rcases family_descends (prefixWord ++ tailWord_150734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150772 : List Nat := [2, 6, 1, 2, 1, 1, 1, 4, 1, 4]
def baseStart_150772 : Nat := 118140960795 + 150772 * 2 ^ 59
def prefixEnd_150772 : Nat := 4983230072969 + 3 ^ 40 * 150772 * 2
def baseEnd_150772 : Nat := 25806168413263112518873

theorem tailTrace_150772 : CollatzResearch.WordTrace tailWord_150772 prefixEnd_150772 25806168413263112518873 := by
  unfold tailWord_150772
  simp only [CollatzResearch.WordTrace]
  refine ⟨2749553304893134326331285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3666071073190845768441713 2749553304893134326331285)
  ·
    refine ⟨128885311166865671546779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2749553304893134326331285 128885311166865671546779)
    ·
      refine ⟨193327966750298507320169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128885311166865671546779 193327966750298507320169)
      ·
        refine ⟨144995975062723880490127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193327966750298507320169 144995975062723880490127)
        ·
          refine ⟨217493962594085820735191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144995975062723880490127 217493962594085820735191)
          ·
            refine ⟨326240943891128731102787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217493962594085820735191 326240943891128731102787)
            ·
              refine ⟨489361415836693096654181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 326240943891128731102787 489361415836693096654181)
              ·
                refine ⟨91755265469379955622659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 489361415836693096654181 91755265469379955622659)
                ·
                  refine ⟨137632898204069933433989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91755265469379955622659 137632898204069933433989)
                  ·
                    refine ⟨25806168413263112518873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 137632898204069933433989 25806168413263112518873)
                    ·
                      rfl

theorem cell23_150772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_150772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_150772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_150772 prefixEnd_150772 := by exact prefixLift 150772
  have htrace : WordTrace (prefixWord ++ tailWord_150772) baseStart_150772 baseEnd_150772 := by
    simpa [prefixWord, tailWord_150772, baseEnd_150772] using wordTrace_append hprefix tailTrace_150772
  have hstable : (prefixWord ++ tailWord_150772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150772).length < 2 ^ (prefixWord ++ tailWord_150772).sum := by decide
  have hdescent : baseEnd_150772 < baseStart_150772 := by decide
  rcases family_descends (prefixWord ++ tailWord_150772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150801 : List Nat := [1, 2, 2, 1, 1, 4, 3, 2, 3, 2, 2]
def baseStart_150801 : Nat := 118140960795 + 150801 * 2 ^ 59
def prefixEnd_150801 : Nat := 4983230072969 + 3 ^ 40 * 150801 * 2
def baseEnd_150801 : Nat := 77433396178769724093985

theorem tailTrace_150801 : CollatzResearch.WordTrace tailWord_150801 prefixEnd_150801 77433396178769724093985 := by
  unfold tailWord_150801
  simp only [CollatzResearch.WordTrace]
  refine ⟨5500164326681206605468257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3666776217787471070312171 5500164326681206605468257)
  ·
    refine ⟨4125123245010904954101193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5500164326681206605468257 4125123245010904954101193)
    ·
      refine ⟨3093842433758178715575895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4125123245010904954101193 3093842433758178715575895)
      ·
        refine ⟨4640763650637268073363843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3093842433758178715575895 4640763650637268073363843)
        ·
          refine ⟨6961145475955902110045765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4640763650637268073363843 6961145475955902110045765)
          ·
            refine ⟨1305214776741731645633581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6961145475955902110045765 1305214776741731645633581)
            ·
              refine ⟨489455541278149367112593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1305214776741731645633581 489455541278149367112593)
              ·
                refine ⟨367091655958612025334445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 489455541278149367112593 367091655958612025334445)
                ·
                  refine ⟨137659370984479509500417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 367091655958612025334445 137659370984479509500417)
                  ·
                    refine ⟨103244528238359632125313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 137659370984479509500417 103244528238359632125313)
                    ·
                      refine ⟨77433396178769724093985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 103244528238359632125313 77433396178769724093985)
                      ·
                        rfl

theorem cell23_150801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 3, 2, 2].length) (baseStart_150801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_150801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_150801 prefixEnd_150801 := by exact prefixLift 150801
  have htrace : WordTrace (prefixWord ++ tailWord_150801) baseStart_150801 baseEnd_150801 := by
    simpa [prefixWord, tailWord_150801, baseEnd_150801] using wordTrace_append hprefix tailTrace_150801
  have hstable : (prefixWord ++ tailWord_150801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150801).length < 2 ^ (prefixWord ++ tailWord_150801).sum := by decide
  have hdescent : baseEnd_150801 < baseStart_150801 := by decide
  rcases family_descends (prefixWord ++ tailWord_150801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150821 : List Nat := [1, 3, 1, 2, 4, 2, 1, 3, 1, 2, 3]
def baseStart_150821 : Nat := 118140960795 + 150821 * 2 ^ 59
def prefixEnd_150821 : Nat := 4983230072969 + 3 ^ 40 * 150821 * 2
def baseEnd_150821 : Nat := 77443665791859645843893

theorem tailTrace_150821 : CollatzResearch.WordTrace tailWord_150821 prefixEnd_150821 77443665791859645843893 := by
  unfold tailWord_150821
  simp only [CollatzResearch.WordTrace]
  refine ⟨5500893786608750021196317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3667262524405833347464211 5500893786608750021196317)
  ·
    refine ⟨2062835169978281257948619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5500893786608750021196317 2062835169978281257948619)
    ·
      refine ⟨3094252754967421886922929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2062835169978281257948619 3094252754967421886922929)
      ·
        refine ⟨2320689566225566415192197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3094252754967421886922929 2320689566225566415192197)
        ·
          refine ⟨435129293667293702848537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2320689566225566415192197 435129293667293702848537)
          ·
            refine ⟨326346970250470277136403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 435129293667293702848537 326346970250470277136403)
            ·
              refine ⟨489520455375705415704605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 326346970250470277136403 489520455375705415704605)
              ·
                refine ⟨183570170765889530889227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 489520455375705415704605 183570170765889530889227)
                ·
                  refine ⟨275355256148834296333841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 183570170765889530889227 275355256148834296333841)
                  ·
                    refine ⟨206516442111625722250381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 275355256148834296333841 206516442111625722250381)
                    ·
                      refine ⟨77443665791859645843893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 206516442111625722250381 77443665791859645843893)
                      ·
                        rfl

theorem cell23_150821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 3, 1, 2, 3].length) (baseStart_150821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_150821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_150821 prefixEnd_150821 := by exact prefixLift 150821
  have htrace : WordTrace (prefixWord ++ tailWord_150821) baseStart_150821 baseEnd_150821 := by
    simpa [prefixWord, tailWord_150821, baseEnd_150821] using wordTrace_append hprefix tailTrace_150821
  have hstable : (prefixWord ++ tailWord_150821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150821).length < 2 ^ (prefixWord ++ tailWord_150821).sum := by decide
  have hdescent : baseEnd_150821 < baseStart_150821 := by decide
  rcases family_descends (prefixWord ++ tailWord_150821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150838 : List Nat := [5, 1, 2, 3, 1, 1, 1, 2, 1, 1, 5]
def baseStart_150838 : Nat := 118140960795 + 150838 * 2 ^ 59
def prefixEnd_150838 : Nat := 4983230072969 + 3 ^ 40 * 150838 * 2
def baseEnd_150838 : Nat := 77452394962986079331315

theorem tailTrace_150838 : CollatzResearch.WordTrace tailWord_150838 prefixEnd_150838 77452394962986079331315 := by
  unfold tailWord_150838
  simp only [CollatzResearch.WordTrace]
  refine ⟨343844614221697620285323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3667675885031441283043445 343844614221697620285323)
  ·
    refine ⟨515766921332546430427985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 343844614221697620285323 515766921332546430427985)
    ·
      refine ⟨386825190999409822820989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 515766921332546430427985 386825190999409822820989)
      ·
        refine ⟨145059446624778683557871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 386825190999409822820989 145059446624778683557871)
        ·
          refine ⟨217589169937168025336807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145059446624778683557871 217589169937168025336807)
          ·
            refine ⟨326383754905752038005211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217589169937168025336807 326383754905752038005211)
            ·
              refine ⟨489575632358628057007817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 326383754905752038005211 489575632358628057007817)
              ·
                refine ⟨367181724268971042755863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 489575632358628057007817 367181724268971042755863)
                ·
                  refine ⟨550772586403456564133795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 367181724268971042755863 550772586403456564133795)
                  ·
                    refine ⟨826158879605184846200693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 550772586403456564133795 826158879605184846200693)
                    ·
                      refine ⟨77452394962986079331315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 826158879605184846200693 77452394962986079331315)
                      ·
                        rfl

theorem cell23_150838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_150838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_150838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_150838 prefixEnd_150838 := by exact prefixLift 150838
  have htrace : WordTrace (prefixWord ++ tailWord_150838) baseStart_150838 baseEnd_150838 := by
    simpa [prefixWord, tailWord_150838, baseEnd_150838] using wordTrace_append hprefix tailTrace_150838
  have hstable : (prefixWord ++ tailWord_150838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150838).length < 2 ^ (prefixWord ++ tailWord_150838).sum := by decide
  have hdescent : baseEnd_150838 < baseStart_150838 := by decide
  rcases family_descends (prefixWord ++ tailWord_150838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150845 : List Nat := [1, 4, 1, 5, 1, 1, 3, 1, 2, 4]
def baseStart_150845 : Nat := 118140960795 + 150845 * 2 ^ 59
def prefixEnd_150845 : Nat := 4983230072969 + 3 ^ 40 * 150845 * 2
def baseEnd_150845 : Nat := 25818663109189183981261

theorem tailTrace_150845 : CollatzResearch.WordTrace tailWord_150845 prefixEnd_150845 25818663109189183981261 := by
  unfold tailWord_150845
  simp only [CollatzResearch.WordTrace]
  refine ⟨5501769138521802120069989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3667846092347868080046659 5501769138521802120069989)
  ·
    refine ⟨1031581713472837897513123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5501769138521802120069989 1031581713472837897513123)
    ·
      refine ⟨1547372570209256846269685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1031581713472837897513123 1547372570209256846269685)
      ·
        refine ⟨145066178457117829337783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1547372570209256846269685 145066178457117829337783)
        ·
          refine ⟨217599267685676744006675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145066178457117829337783 217599267685676744006675)
          ·
            refine ⟨326398901528515116010013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217599267685676744006675 326398901528515116010013)
            ·
              refine ⟨122399588073193168503755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 326398901528515116010013 122399588073193168503755)
              ·
                refine ⟨183599382109789752755633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122399588073193168503755 183599382109789752755633)
                ·
                  refine ⟨137699536582342314566725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 183599382109789752755633 137699536582342314566725)
                  ·
                    refine ⟨25818663109189183981261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 137699536582342314566725 25818663109189183981261)
                    ·
                      rfl

theorem cell23_150845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 1, 2, 4].length) (baseStart_150845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_150845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_150845 prefixEnd_150845 := by exact prefixLift 150845
  have htrace : WordTrace (prefixWord ++ tailWord_150845) baseStart_150845 baseEnd_150845 := by
    simpa [prefixWord, tailWord_150845, baseEnd_150845] using wordTrace_append hprefix tailTrace_150845
  have hstable : (prefixWord ++ tailWord_150845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150845).length < 2 ^ (prefixWord ++ tailWord_150845).sum := by decide
  have hdescent : baseEnd_150845 < baseStart_150845 := by decide
  rcases family_descends (prefixWord ++ tailWord_150845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150857 : List Nat := [1, 2, 1, 1, 2, 3, 2, 2, 2, 3, 4]
def baseStart_150857 : Nat := 118140960795 + 150857 * 2 ^ 59
def prefixEnd_150857 : Nat := 4983230072969 + 3 ^ 40 * 150857 * 2
def baseEnd_150857 : Nat := 77462151095421504993727

theorem tailTrace_150857 : CollatzResearch.WordTrace tailWord_150857 prefixEnd_150857 77462151095421504993727 := by
  unfold tailWord_150857
  simp only [CollatzResearch.WordTrace]
  refine ⟨5502206814478328169506825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3668137876318885446337883 5502206814478328169506825)
  ·
    refine ⟨4126655110858746127130119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5502206814478328169506825 4126655110858746127130119)
    ·
      refine ⟨6189982666288119190695179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4126655110858746127130119 6189982666288119190695179)
      ·
        refine ⟨9284973999432178786042769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6189982666288119190695179 9284973999432178786042769)
        ·
          refine ⟨6963730499574134089532077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9284973999432178786042769 6963730499574134089532077)
          ·
            refine ⟨2611398937340300283574529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6963730499574134089532077 2611398937340300283574529)
            ·
              refine ⟨1958549203005225212680897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2611398937340300283574529 1958549203005225212680897)
              ·
                refine ⟨1468911902253918909510673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1958549203005225212680897 1468911902253918909510673)
                ·
                  refine ⟨1101683926690439182133005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1468911902253918909510673 1101683926690439182133005)
                  ·
                    refine ⟨413131472508914693299877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1101683926690439182133005 413131472508914693299877)
                    ·
                      refine ⟨77462151095421504993727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 413131472508914693299877 77462151095421504993727)
                      ·
                        rfl

theorem cell23_150857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 3, 4].length) (baseStart_150857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_150857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_150857 prefixEnd_150857 := by exact prefixLift 150857
  have htrace : WordTrace (prefixWord ++ tailWord_150857) baseStart_150857 baseEnd_150857 := by
    simpa [prefixWord, tailWord_150857, baseEnd_150857] using wordTrace_append hprefix tailTrace_150857
  have hstable : (prefixWord ++ tailWord_150857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150857).length < 2 ^ (prefixWord ++ tailWord_150857).sum := by decide
  have hdescent : baseEnd_150857 < baseStart_150857 := by decide
  rcases family_descends (prefixWord ++ tailWord_150857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150908 : List Nat := [2, 2, 2, 1, 1, 1, 5, 3, 2, 2, 2]
def baseStart_150908 : Nat := 118140960795 + 150908 * 2 ^ 59
def prefixEnd_150908 : Nat := 4983230072969 + 3 ^ 40 * 150908 * 2
def baseEnd_150908 : Nat := 77488338608800805455993

theorem tailTrace_150908 : CollatzResearch.WordTrace tailWord_150908 prefixEnd_150908 77488338608800805455993 := by
  unfold tailWord_150908
  simp only [CollatzResearch.WordTrace]
  refine ⟨2752033468646781939806689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3669377958195709253075585 2752033468646781939806689)
  ·
    refine ⟨2064025101485086454855017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2752033468646781939806689 2064025101485086454855017)
    ·
      refine ⟨1548018826113814841141263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2064025101485086454855017 1548018826113814841141263)
      ·
        refine ⟨2322028239170722261711895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1548018826113814841141263 2322028239170722261711895)
        ·
          refine ⟨3483042358756083392567843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2322028239170722261711895 3483042358756083392567843)
          ·
            refine ⟨5224563538134125088851765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3483042358756083392567843 5224563538134125088851765)
            ·
              refine ⟨489802831700074227079853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5224563538134125088851765 489802831700074227079853)
              ·
                refine ⟨183676061887527835154945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 489802831700074227079853 183676061887527835154945)
                ·
                  refine ⟨137757046415645876366209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 183676061887527835154945 137757046415645876366209)
                  ·
                    refine ⟨103317784811734407274657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 137757046415645876366209 103317784811734407274657)
                    ·
                      refine ⟨77488338608800805455993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 103317784811734407274657 77488338608800805455993)
                      ·
                        rfl

theorem cell23_150908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 3, 2, 2, 2].length) (baseStart_150908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_150908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_150908 prefixEnd_150908 := by exact prefixLift 150908
  have htrace : WordTrace (prefixWord ++ tailWord_150908) baseStart_150908 baseEnd_150908 := by
    simpa [prefixWord, tailWord_150908, baseEnd_150908] using wordTrace_append hprefix tailTrace_150908
  have hstable : (prefixWord ++ tailWord_150908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150908).length < 2 ^ (prefixWord ++ tailWord_150908).sum := by decide
  have hdescent : baseEnd_150908 < baseStart_150908 := by decide
  rcases family_descends (prefixWord ++ tailWord_150908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150944 : List Nat := [2, 1, 1, 4, 1, 2, 1, 4, 2, 5]
def baseStart_150944 : Nat := 118140960795 + 150944 * 2 ^ 59
def prefixEnd_150944 : Nat := 4983230072969 + 3 ^ 40 * 150944 * 2
def baseEnd_150944 : Nat := 25835607970787554868609

theorem tailTrace_150944 : CollatzResearch.WordTrace tailWord_150944 prefixEnd_150944 25835607970787554868609 := by
  unfold tailWord_150944
  simp only [CollatzResearch.WordTrace]
  refine ⟨2752689982581571013961943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3670253310108761351949257 2752689982581571013961943)
  ·
    refine ⟨4129034973872356520942915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2752689982581571013961943 4129034973872356520942915)
    ·
      refine ⟨6193552460808534781414373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4129034973872356520942915 6193552460808534781414373)
      ·
        refine ⟨1161291086401600271515195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6193552460808534781414373 1161291086401600271515195)
        ·
          refine ⟨1741936629602400407272793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1161291086401600271515195 1741936629602400407272793)
          ·
            refine ⟨1306452472201800305454595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1741936629602400407272793 1306452472201800305454595)
            ·
              refine ⟨1959678708302700458181893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1306452472201800305454595 1959678708302700458181893)
              ·
                refine ⟨367439757806756335909105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1959678708302700458181893 367439757806756335909105)
                ·
                  refine ⟨275579818355067251931829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 367439757806756335909105 275579818355067251931829)
                  ·
                    refine ⟨25835607970787554868609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 275579818355067251931829 25835607970787554868609)
                    ·
                      rfl

theorem cell23_150944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 4, 2, 5].length) (baseStart_150944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_150944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_150944 prefixEnd_150944 := by exact prefixLift 150944
  have htrace : WordTrace (prefixWord ++ tailWord_150944) baseStart_150944 baseEnd_150944 := by
    simpa [prefixWord, tailWord_150944, baseEnd_150944] using wordTrace_append hprefix tailTrace_150944
  have hstable : (prefixWord ++ tailWord_150944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150944).length < 2 ^ (prefixWord ++ tailWord_150944).sum := by decide
  have hdescent : baseEnd_150944 < baseStart_150944 := by decide
  rcases family_descends (prefixWord ++ tailWord_150944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150951 : List Nat := [1, 1, 6, 1, 1, 1, 1, 1, 1, 7, 2]
def baseStart_150951 : Nat := 118140960795 + 150951 * 2 ^ 59
def prefixEnd_150951 : Nat := 4983230072969 + 3 ^ 40 * 150951 * 2
def baseEnd_150951 : Nat := 77510418276944137218295

theorem tailTrace_150951 : CollatzResearch.WordTrace tailWord_150951 prefixEnd_150951 77510418276944137218295 := by
  unfold tailWord_150951
  simp only [CollatzResearch.WordTrace]
  refine ⟨5505635276137782223428707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3670423517425188148952471 5505635276137782223428707)
  ·
    refine ⟨8258452914206673335143061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5505635276137782223428707 8258452914206673335143061)
    ·
      refine ⟨387114980353437812584831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8258452914206673335143061 387114980353437812584831)
      ·
        refine ⟨580672470530156718877247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 387114980353437812584831 580672470530156718877247)
        ·
          refine ⟨871008705795235078315871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 580672470530156718877247 871008705795235078315871)
          ·
            refine ⟨1306513058692852617473807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 871008705795235078315871 1306513058692852617473807)
            ·
              refine ⟨1959769588039278926210711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1306513058692852617473807 1959769588039278926210711)
              ·
                refine ⟨2939654382058918389316067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1959769588039278926210711 2939654382058918389316067)
                ·
                  refine ⟨4409481573088377583974101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2939654382058918389316067 4409481573088377583974101)
                  ·
                    refine ⟨103347224369258849624393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4409481573088377583974101 103347224369258849624393)
                    ·
                      refine ⟨77510418276944137218295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 103347224369258849624393 77510418276944137218295)
                      ·
                        rfl

theorem cell23_150951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_150951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_150951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_150951 prefixEnd_150951 := by exact prefixLift 150951
  have htrace : WordTrace (prefixWord ++ tailWord_150951) baseStart_150951 baseEnd_150951 := by
    simpa [prefixWord, tailWord_150951, baseEnd_150951] using wordTrace_append hprefix tailTrace_150951
  have hstable : (prefixWord ++ tailWord_150951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150951).length < 2 ^ (prefixWord ++ tailWord_150951).sum := by decide
  have hdescent : baseEnd_150951 < baseStart_150951 := by decide
  rcases family_descends (prefixWord ++ tailWord_150951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151031 : List Nat := [1, 1, 3, 1, 1, 1, 1, 5, 5, 1, 3]
def baseStart_151031 : Nat := 118140960795 + 151031 * 2 ^ 59
def prefixEnd_151031 : Nat := 4983230072969 + 3 ^ 40 * 151031 * 2
def baseEnd_151031 : Nat := 77551496729303824217927

theorem tailTrace_151031 : CollatzResearch.WordTrace tailWord_151031 prefixEnd_151031 77551496729303824217927 := by
  unfold tailWord_151031
  simp only [CollatzResearch.WordTrace]
  refine ⟨5508553115847955886340947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3672368743898637257560631 5508553115847955886340947)
  ·
    refine ⟨8262829673771933829511421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5508553115847955886340947 8262829673771933829511421)
    ·
      refine ⟨3098561127664475186066783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8262829673771933829511421 3098561127664475186066783)
      ·
        refine ⟨4647841691496712779100175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3098561127664475186066783 4647841691496712779100175)
        ·
          refine ⟨6971762537245069168650263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4647841691496712779100175 6971762537245069168650263)
          ·
            refine ⟨10457643805867603752975395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6971762537245069168650263 10457643805867603752975395)
            ·
              refine ⟨15686465708801405629463093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10457643805867603752975395 15686465708801405629463093)
              ·
                refine ⟨1470606160200131777762165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15686465708801405629463093 1470606160200131777762165)
                ·
                  refine ⟨137869327518762354165203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1470606160200131777762165 137869327518762354165203)
                  ·
                    refine ⟨206803991278143531247805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 137869327518762354165203 206803991278143531247805)
                    ·
                      refine ⟨77551496729303824217927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 206803991278143531247805 77551496729303824217927)
                      ·
                        rfl

theorem cell23_151031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 5, 1, 3].length) (baseStart_151031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151031 prefixEnd_151031 := by exact prefixLift 151031
  have htrace : WordTrace (prefixWord ++ tailWord_151031) baseStart_151031 baseEnd_151031 := by
    simpa [prefixWord, tailWord_151031, baseEnd_151031] using wordTrace_append hprefix tailTrace_151031
  have hstable : (prefixWord ++ tailWord_151031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151031).length < 2 ^ (prefixWord ++ tailWord_151031).sum := by decide
  have hdescent : baseEnd_151031 < baseStart_151031 := by decide
  rcases family_descends (prefixWord ++ tailWord_151031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151042 : List Nat := [3, 4, 1, 2, 1, 1, 3, 3, 1, 4]
def baseStart_151042 : Nat := 118140960795 + 151042 * 2 ^ 59
def prefixEnd_151042 : Nat := 4983230072969 + 3 ^ 40 * 151042 * 2
def baseEnd_151042 : Nat := 25852381672167760393459

theorem tailTrace_151042 : CollatzResearch.WordTrace tailWord_151042 prefixEnd_151042 25852381672167760393459 := by
  unfold tailWord_151042
  simp only [CollatzResearch.WordTrace]
  refine ⟨1377238579702026191247845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3672636212538736509994253 1377238579702026191247845)
  ·
    refine ⟨258232233694129910858971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1377238579702026191247845 258232233694129910858971)
    ·
      refine ⟨387348350541194866288457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258232233694129910858971 387348350541194866288457)
      ·
        refine ⟨290511262905896149716343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 387348350541194866288457 290511262905896149716343)
        ·
          refine ⟨435766894358844224574515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290511262905896149716343 435766894358844224574515)
          ·
            refine ⟨653650341538266336861773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 435766894358844224574515 653650341538266336861773)
            ·
              refine ⟨245118878076849876323165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 653650341538266336861773 245118878076849876323165)
              ·
                refine ⟨91919579278818703621187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 245118878076849876323165 91919579278818703621187)
                ·
                  refine ⟨137879368918228055431781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91919579278818703621187 137879368918228055431781)
                  ·
                    refine ⟨25852381672167760393459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 137879368918228055431781 25852381672167760393459)
                    ·
                      rfl

theorem cell23_151042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_151042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151042 prefixEnd_151042 := by exact prefixLift 151042
  have htrace : WordTrace (prefixWord ++ tailWord_151042) baseStart_151042 baseEnd_151042 := by
    simpa [prefixWord, tailWord_151042, baseEnd_151042] using wordTrace_append hprefix tailTrace_151042
  have hstable : (prefixWord ++ tailWord_151042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151042).length < 2 ^ (prefixWord ++ tailWord_151042).sum := by decide
  have hdescent : baseEnd_151042 < baseStart_151042 := by decide
  rcases family_descends (prefixWord ++ tailWord_151042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151088 : List Nat := [2, 1, 1, 1, 2, 3, 1, 3, 5, 2, 2]
def baseStart_151088 : Nat := 118140960795 + 151088 * 2 ^ 59
def prefixEnd_151088 : Nat := 4983230072969 + 3 ^ 40 * 151088 * 2
def baseEnd_151088 : Nat := 77580765126610101205165

theorem tailTrace_151088 : CollatzResearch.WordTrace tailWord_151088 prefixEnd_151088 77580765126610101205165 := by
  unfold tailWord_151088
  simp only [CollatzResearch.WordTrace]
  refine ⟨2755316038320727310582959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3673754717760969747443945 2755316038320727310582959)
  ·
    refine ⟨4132974057481090965874439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2755316038320727310582959 4132974057481090965874439)
    ·
      refine ⟨6199461086221636448811659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4132974057481090965874439 6199461086221636448811659)
      ·
        refine ⟨9299191629332454673217489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6199461086221636448811659 9299191629332454673217489)
        ·
          refine ⟨6974393721999341004913117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9299191629332454673217489 6974393721999341004913117)
          ·
            refine ⟨2615397645749752876842419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6974393721999341004913117 2615397645749752876842419)
            ·
              refine ⟨3923096468624629315263629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2615397645749752876842419 3923096468624629315263629)
              ·
                refine ⟨1471161175734235993223861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3923096468624629315263629 1471161175734235993223861)
                ·
                  refine ⟨137921360225084624364737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1471161175734235993223861 137921360225084624364737)
                  ·
                    refine ⟨103441020168813468273553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 137921360225084624364737 103441020168813468273553)
                    ·
                      refine ⟨77580765126610101205165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 103441020168813468273553 77580765126610101205165)
                      ·
                        rfl

theorem cell23_151088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 5, 2, 2].length) (baseStart_151088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151088 prefixEnd_151088 := by exact prefixLift 151088
  have htrace : WordTrace (prefixWord ++ tailWord_151088) baseStart_151088 baseEnd_151088 := by
    simpa [prefixWord, tailWord_151088, baseEnd_151088] using wordTrace_append hprefix tailTrace_151088
  have hstable : (prefixWord ++ tailWord_151088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151088).length < 2 ^ (prefixWord ++ tailWord_151088).sum := by decide
  have hdescent : baseEnd_151088 < baseStart_151088 := by decide
  rcases family_descends (prefixWord ++ tailWord_151088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151105 : List Nat := [1, 2, 5, 1, 1, 1, 5, 1, 1, 1, 4]
def baseStart_151105 : Nat := 118140960795 + 151105 * 2 ^ 59
def prefixEnd_151105 : Nat := 4983230072969 + 3 ^ 40 * 151105 * 2
def baseEnd_151105 : Nat := 77589494297736534692587

theorem tailTrace_151105 : CollatzResearch.WordTrace tailWord_151105 prefixEnd_151105 77589494297736534692587 := by
  unfold tailWord_151105
  simp only [CollatzResearch.WordTrace]
  refine ⟨5511252117579866524534769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3674168078386577683023179 5511252117579866524534769)
  ·
    refine ⟨4133439088184899893401077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5511252117579866524534769 4133439088184899893401077)
    ·
      refine ⟨387509914517334365006351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4133439088184899893401077 387509914517334365006351)
      ·
        refine ⟨581264871776001547509527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 387509914517334365006351 581264871776001547509527)
        ·
          refine ⟨871897307664002321264291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 581264871776001547509527 871897307664002321264291)
          ·
            refine ⟨1307845961496003481896437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 871897307664002321264291 1307845961496003481896437)
            ·
              refine ⟨122610558890250326427791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1307845961496003481896437 122610558890250326427791)
              ·
                refine ⟨183915838335375489641687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122610558890250326427791 183915838335375489641687)
                ·
                  refine ⟨275873757503063234462531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 183915838335375489641687 275873757503063234462531)
                  ·
                    refine ⟨413810636254594851693797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 275873757503063234462531 413810636254594851693797)
                    ·
                      refine ⟨77589494297736534692587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 413810636254594851693797 77589494297736534692587)
                      ·
                        rfl

theorem cell23_151105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_151105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151105 prefixEnd_151105 := by exact prefixLift 151105
  have htrace : WordTrace (prefixWord ++ tailWord_151105) baseStart_151105 baseEnd_151105 := by
    simpa [prefixWord, tailWord_151105, baseEnd_151105] using wordTrace_append hprefix tailTrace_151105
  have hstable : (prefixWord ++ tailWord_151105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151105).length < 2 ^ (prefixWord ++ tailWord_151105).sum := by decide
  have hdescent : baseEnd_151105 < baseStart_151105 := by decide
  rcases family_descends (prefixWord ++ tailWord_151105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151111 : List Nat := [1, 1, 4, 1, 6, 10]
def baseStart_151111 : Nat := 118140960795 + 151111 * 2 ^ 59
def prefixEnd_151111 : Nat := 4983230072969 + 3 ^ 40 * 151111 * 2
def baseEnd_151111 : Nat := 319311008978039140813

theorem tailTrace_151111 : CollatzResearch.WordTrace tailWord_151111 prefixEnd_151111 319311008978039140813 := by
  unfold tailWord_151111
  simp only [CollatzResearch.WordTrace]
  refine ⟨5511470955558129549253187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3674313970372086366168791 5511470955558129549253187)
  ·
    refine ⟨8267206433337194323879781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5511470955558129549253187 8267206433337194323879781)
    ·
      refine ⟨1550101206250723935727459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8267206433337194323879781 1550101206250723935727459)
      ·
        refine ⟨2325151809376085903591189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1550101206250723935727459 2325151809376085903591189)
        ·
          refine ⟨108991491064504026730837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2325151809376085903591189 108991491064504026730837)
          ·
            refine ⟨319311008978039140813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 108991491064504026730837 319311008978039140813)
            ·
              rfl

theorem cell23_151111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 10].length) (baseStart_151111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151111 prefixEnd_151111 := by exact prefixLift 151111
  have htrace : WordTrace (prefixWord ++ tailWord_151111) baseStart_151111 baseEnd_151111 := by
    simpa [prefixWord, tailWord_151111, baseEnd_151111] using wordTrace_append hprefix tailTrace_151111
  have hstable : (prefixWord ++ tailWord_151111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151111).length < 2 ^ (prefixWord ++ tailWord_151111).sum := by decide
  have hdescent : baseEnd_151111 < baseStart_151111 := by decide
  rcases family_descends (prefixWord ++ tailWord_151111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151121 : List Nat := [1, 2, 2, 1, 3, 2, 1, 2, 3, 3, 3]
def baseStart_151121 : Nat := 118140960795 + 151121 * 2 ^ 59
def prefixEnd_151121 : Nat := 4983230072969 + 3 ^ 40 * 151121 * 2
def baseEnd_151121 : Nat := 77597709988208472092513

theorem tailTrace_151121 : CollatzResearch.WordTrace tailWord_151121 prefixEnd_151121 77597709988208472092513 := by
  unfold tailWord_151121
  simp only [CollatzResearch.WordTrace]
  refine ⟨5511835685521901257117217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3674557123681267504744811 5511835685521901257117217)
  ·
    refine ⟨4133876764141425942837913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5511835685521901257117217 4133876764141425942837913)
    ·
      refine ⟨3100407573106069457128435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4133876764141425942837913 3100407573106069457128435)
      ·
        refine ⟨4650611359659104185692653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3100407573106069457128435 4650611359659104185692653)
        ·
          refine ⟨1743979259872164069634745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4650611359659104185692653 1743979259872164069634745)
          ·
            refine ⟨1307984444904123052226059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1743979259872164069634745 1307984444904123052226059)
            ·
              refine ⟨1961976667356184578339089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1307984444904123052226059 1961976667356184578339089)
              ·
                refine ⟨1471482500517138433754317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1961976667356184578339089 1471482500517138433754317)
                ·
                  refine ⟨551805937693926912657869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1471482500517138433754317 551805937693926912657869)
                  ·
                    refine ⟨206927226635222592246701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 551805937693926912657869 206927226635222592246701)
                    ·
                      refine ⟨77597709988208472092513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 206927226635222592246701 77597709988208472092513)
                      ·
                        rfl

theorem cell23_151121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 3, 3].length) (baseStart_151121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151121 prefixEnd_151121 := by exact prefixLift 151121
  have htrace : WordTrace (prefixWord ++ tailWord_151121) baseStart_151121 baseEnd_151121 := by
    simpa [prefixWord, tailWord_151121, baseEnd_151121] using wordTrace_append hprefix tailTrace_151121
  have hstable : (prefixWord ++ tailWord_151121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151121).length < 2 ^ (prefixWord ++ tailWord_151121).sum := by decide
  have hdescent : baseEnd_151121 < baseStart_151121 := by decide
  rcases family_descends (prefixWord ++ tailWord_151121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151199 : List Nat := [1, 1, 2, 7, 1, 1, 2, 2, 1, 3, 2]
def baseStart_151199 : Nat := 118140960795 + 151199 * 2 ^ 59
def prefixEnd_151199 : Nat := 4983230072969 + 3 ^ 40 * 151199 * 2
def baseEnd_151199 : Nat := 77637761479259166917155

theorem tailTrace_151199 : CollatzResearch.WordTrace tailWord_151199 prefixEnd_151199 77637761479259166917155 := by
  unfold tailWord_151199
  simp only [CollatzResearch.WordTrace]
  refine ⟨5514680579239320578456651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3676453719492880385637767 5514680579239320578456651)
  ·
    refine ⟨8272020868858980867684977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5514680579239320578456651 8272020868858980867684977)
    ·
      refine ⟨6204015651644235650763733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8272020868858980867684977 6204015651644235650763733)
      ·
        refine ⟨145406616835411773064775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 6204015651644235650763733 145406616835411773064775)
        ·
          refine ⟨218109925253117659597163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145406616835411773064775 218109925253117659597163)
          ·
            refine ⟨327164887879676489395745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218109925253117659597163 327164887879676489395745)
            ·
              refine ⟨245373665909757367046809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 327164887879676489395745 245373665909757367046809)
              ·
                refine ⟨184030249432318025285107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 245373665909757367046809 184030249432318025285107)
                ·
                  refine ⟨276045374148477037927661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 184030249432318025285107 276045374148477037927661)
                  ·
                    refine ⟨103517015305678889222873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 276045374148477037927661 103517015305678889222873)
                    ·
                      refine ⟨77637761479259166917155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 103517015305678889222873 77637761479259166917155)
                      ·
                        rfl

theorem cell23_151199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_151199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151199 prefixEnd_151199 := by exact prefixLift 151199
  have htrace : WordTrace (prefixWord ++ tailWord_151199) baseStart_151199 baseEnd_151199 := by
    simpa [prefixWord, tailWord_151199, baseEnd_151199] using wordTrace_append hprefix tailTrace_151199
  have hstable : (prefixWord ++ tailWord_151199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151199).length < 2 ^ (prefixWord ++ tailWord_151199).sum := by decide
  have hdescent : baseEnd_151199 < baseStart_151199 := by decide
  rcases family_descends (prefixWord ++ tailWord_151199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151265 : List Nat := [1, 2, 3, 1, 5, 1, 2, 1, 2, 5]
def baseStart_151265 : Nat := 118140960795 + 151265 * 2 ^ 59
def prefixEnd_151265 : Nat := 4983230072969 + 3 ^ 40 * 151265 * 2
def baseEnd_151265 : Nat := 25890550400818636230617

theorem tailTrace_151265 : CollatzResearch.WordTrace tailWord_151265 prefixEnd_151265 25890550400818636230617 := by
  unfold tailWord_151265
  simp only [CollatzResearch.WordTrace]
  refine ⟨5517087797000213850359249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3678058531333475900239499 5517087797000213850359249)
  ·
    refine ⟨4137815847750160387769437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5517087797000213850359249 4137815847750160387769437)
    ·
      refine ⟨1551680942906310145413539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4137815847750160387769437 1551680942906310145413539)
      ·
        refine ⟨2327521414359465218120309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1551680942906310145413539 2327521414359465218120309)
        ·
          refine ⟨218205132596199864198779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2327521414359465218120309 218205132596199864198779)
          ·
            refine ⟨327307698894299796298169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218205132596199864198779 327307698894299796298169)
            ·
              refine ⟨245480774170724847223627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 327307698894299796298169 245480774170724847223627)
              ·
                refine ⟨368221161256087270835441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 245480774170724847223627 368221161256087270835441)
                ·
                  refine ⟨276165870942065453126581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 368221161256087270835441 276165870942065453126581)
                  ·
                    refine ⟨25890550400818636230617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 276165870942065453126581 25890550400818636230617)
                    ·
                      rfl

theorem cell23_151265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 1, 2, 5].length) (baseStart_151265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151265 prefixEnd_151265 := by exact prefixLift 151265
  have htrace : WordTrace (prefixWord ++ tailWord_151265) baseStart_151265 baseEnd_151265 := by
    simpa [prefixWord, tailWord_151265, baseEnd_151265] using wordTrace_append hprefix tailTrace_151265
  have hstable : (prefixWord ++ tailWord_151265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151265).length < 2 ^ (prefixWord ++ tailWord_151265).sum := by decide
  have hdescent : baseEnd_151265 < baseStart_151265 := by decide
  rcases family_descends (prefixWord ++ tailWord_151265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151288 : List Nat := [2, 1, 2, 1, 1, 2, 2, 3, 4, 2, 3]
def baseStart_151288 : Nat := 118140960795 + 151288 * 2 ^ 59
def prefixEnd_151288 : Nat := 4983230072969 + 3 ^ 40 * 151288 * 2
def baseEnd_151288 : Nat := 77683461257509318704245

theorem tailTrace_151288 : CollatzResearch.WordTrace tailWord_151288 prefixEnd_151288 77683461257509318704245 := by
  unfold tailWord_151288
  simp only [CollatzResearch.WordTrace]
  refine ⟨2758963337958444389223259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3678617783944592518964345 2758963337958444389223259)
  ·
    refine ⟨4138445006937666583834889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2758963337958444389223259 4138445006937666583834889)
    ·
      refine ⟨3103833755203249937876167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4138445006937666583834889 3103833755203249937876167)
      ·
        refine ⟨4655750632804874906814251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3103833755203249937876167 4655750632804874906814251)
        ·
          refine ⟨6983625949207312360221377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4655750632804874906814251 6983625949207312360221377)
          ·
            refine ⟨5237719461905484270166033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6983625949207312360221377 5237719461905484270166033)
            ·
              refine ⟨3928289596429113202624525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5237719461905484270166033 3928289596429113202624525)
              ·
                refine ⟨1473108598660917450984197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3928289596429113202624525 1473108598660917450984197)
                ·
                  refine ⟨276207862248922022059537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1473108598660917450984197 276207862248922022059537)
                  ·
                    refine ⟨207155896686691516544653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 276207862248922022059537 207155896686691516544653)
                    ·
                      refine ⟨77683461257509318704245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 207155896686691516544653 77683461257509318704245)
                      ·
                        rfl

theorem cell23_151288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 4, 2, 3].length) (baseStart_151288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151288 prefixEnd_151288 := by exact prefixLift 151288
  have htrace : WordTrace (prefixWord ++ tailWord_151288) baseStart_151288 baseEnd_151288 := by
    simpa [prefixWord, tailWord_151288, baseEnd_151288] using wordTrace_append hprefix tailTrace_151288
  have hstable : (prefixWord ++ tailWord_151288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151288).length < 2 ^ (prefixWord ++ tailWord_151288).sum := by decide
  have hdescent : baseEnd_151288 < baseStart_151288 := by decide
  rcases family_descends (prefixWord ++ tailWord_151288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151308 : List Nat := [2, 2, 1, 2, 2, 1, 4, 3, 6]
def baseStart_151308 : Nat := 118140960795 + 151308 * 2 ^ 59
def prefixEnd_151308 : Nat := 4983230072969 + 3 ^ 40 * 151308 * 2
def baseEnd_151308 : Nat := 8632636763399915606017

theorem tailTrace_151308 : CollatzResearch.WordTrace tailWord_151308 prefixEnd_151308 8632636763399915606017 := by
  unfold tailWord_151308
  simp only [CollatzResearch.WordTrace]
  refine ⟨2759328067922216097087289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3679104090562954796116385 2759328067922216097087289)
  ·
    refine ⟨2069496050941662072815467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2759328067922216097087289 2069496050941662072815467)
    ·
      refine ⟨3104244076412493109223201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2069496050941662072815467 3104244076412493109223201)
      ·
        refine ⟨2328183057309369831917401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3104244076412493109223201 2328183057309369831917401)
        ·
          refine ⟨1746137292982027373938051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2328183057309369831917401 1746137292982027373938051)
          ·
            refine ⟨2619205939473041060907077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1746137292982027373938051 2619205939473041060907077)
            ·
              refine ⟨491101113651195198920077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2619205939473041060907077 491101113651195198920077)
              ·
                refine ⟨184162917619198199595029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 491101113651195198920077 184162917619198199595029)
                ·
                  refine ⟨8632636763399915606017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 184162917619198199595029 8632636763399915606017)
                  ·
                    rfl

theorem cell23_151308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 3, 6].length) (baseStart_151308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151308 prefixEnd_151308 := by exact prefixLift 151308
  have htrace : WordTrace (prefixWord ++ tailWord_151308) baseStart_151308 baseEnd_151308 := by
    simpa [prefixWord, tailWord_151308, baseEnd_151308] using wordTrace_append hprefix tailTrace_151308
  have hstable : (prefixWord ++ tailWord_151308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151308).length < 2 ^ (prefixWord ++ tailWord_151308).sum := by decide
  have hdescent : baseEnd_151308 < baseStart_151308 := by decide
  rcases family_descends (prefixWord ++ tailWord_151308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151311 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 6]
def baseStart_151311 : Nat := 118140960795 + 151311 * 2 ^ 59
def prefixEnd_151311 : Nat := 4983230072969 + 3 ^ 40 * 151311 * 2
def baseEnd_151311 : Nat := 77695271312562728716639

theorem tailTrace_151311 : CollatzResearch.WordTrace tailWord_151311 prefixEnd_151311 77695271312562728716639 := by
  unfold tailWord_151311
  simp only [CollatzResearch.WordTrace]
  refine ⟨5518765554833563706533787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3679177036555709137689191 5518765554833563706533787)
  ·
    refine ⟨8278148332250345559800681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5518765554833563706533787 8278148332250345559800681)
    ·
      refine ⟨6208611249187759169850511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8278148332250345559800681 6208611249187759169850511)
      ·
        refine ⟨9312916873781638754775767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6208611249187759169850511 9312916873781638754775767)
        ·
          refine ⟨13969375310672458132163651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9312916873781638754775767 13969375310672458132163651)
          ·
            refine ⟨20954062966008687198245477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13969375310672458132163651 20954062966008687198245477)
            ·
              refine ⟨3928886806126628849671027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20954062966008687198245477 3928886806126628849671027)
              ·
                refine ⟨5893330209189943274506541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3928886806126628849671027 5893330209189943274506541)
                ·
                  refine ⟨2209998828446228727939953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5893330209189943274506541 2209998828446228727939953)
                  ·
                    refine ⟨1657499121334671545954965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2209998828446228727939953 1657499121334671545954965)
                    ·
                      refine ⟨77695271312562728716639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1657499121334671545954965 77695271312562728716639)
                      ·
                        rfl

theorem cell23_151311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 6].length) (baseStart_151311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151311 prefixEnd_151311 := by exact prefixLift 151311
  have htrace : WordTrace (prefixWord ++ tailWord_151311) baseStart_151311 baseEnd_151311 := by
    simpa [prefixWord, tailWord_151311, baseEnd_151311] using wordTrace_append hprefix tailTrace_151311
  have hstable : (prefixWord ++ tailWord_151311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151311).length < 2 ^ (prefixWord ++ tailWord_151311).sum := by decide
  have hdescent : baseEnd_151311 < baseStart_151311 := by decide
  rcases family_descends (prefixWord ++ tailWord_151311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151316 : List Nat := [2, 4, 4, 1, 1, 2, 1, 1, 2, 5]
def baseStart_151316 : Nat := 118140960795 + 151316 * 2 ^ 59
def prefixEnd_151316 : Nat := 4983230072969 + 3 ^ 40 * 151316 * 2
def baseEnd_151316 : Nat := 25899279571945069718039

theorem tailTrace_151316 : CollatzResearch.WordTrace tailWord_151316 prefixEnd_151316 25899279571945069718039 := by
  unfold tailWord_151316
  simp only [CollatzResearch.WordTrace]
  refine ⟨2759473959907724780232901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3679298613210299706977201 2759473959907724780232901)
  ·
    refine ⟨517401367482698396293669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2759473959907724780232901 517401367482698396293669)
    ·
      refine ⟨97012756403005949305063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 517401367482698396293669 97012756403005949305063)
      ·
        refine ⟨145519134604508923957595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97012756403005949305063 145519134604508923957595)
        ·
          refine ⟨218278701906763385936393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145519134604508923957595 218278701906763385936393)
          ·
            refine ⟨163709026430072539452295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 218278701906763385936393 163709026430072539452295)
            ·
              refine ⟨245563539645108809178443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163709026430072539452295 245563539645108809178443)
              ·
                refine ⟨368345309467663213767665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 245563539645108809178443 368345309467663213767665)
                ·
                  refine ⟨276258982100747410325749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 368345309467663213767665 276258982100747410325749)
                  ·
                    refine ⟨25899279571945069718039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 276258982100747410325749 25899279571945069718039)
                    ·
                      rfl

theorem cell23_151316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_151316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151316 prefixEnd_151316 := by exact prefixLift 151316
  have htrace : WordTrace (prefixWord ++ tailWord_151316) baseStart_151316 baseEnd_151316 := by
    simpa [prefixWord, tailWord_151316, baseEnd_151316] using wordTrace_append hprefix tailTrace_151316
  have hstable : (prefixWord ++ tailWord_151316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151316).length < 2 ^ (prefixWord ++ tailWord_151316).sum := by decide
  have hdescent : baseEnd_151316 < baseStart_151316 := by decide
  rcases family_descends (prefixWord ++ tailWord_151316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151322 : List Nat := [3, 1, 1, 3, 2, 4, 1, 1, 2, 2, 3]
def baseStart_151322 : Nat := 118140960795 + 151322 * 2 ^ 59
def prefixEnd_151322 : Nat := 4983230072969 + 3 ^ 40 * 151322 * 2
def baseEnd_151322 : Nat := 77700919599762185679089

theorem tailTrace_151322 : CollatzResearch.WordTrace tailWord_151322 prefixEnd_151322 77700919599762185679089 := by
  unfold tailWord_151322
  simp only [CollatzResearch.WordTrace]
  refine ⟨1379791689448428146296055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3679444505195808390122813 1379791689448428146296055)
  ·
    refine ⟨2069687534172642219444083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1379791689448428146296055 2069687534172642219444083)
    ·
      refine ⟨3104531301258963329166125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2069687534172642219444083 3104531301258963329166125)
      ·
        refine ⟨1164199237972111248437297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3104531301258963329166125 1164199237972111248437297)
        ·
          refine ⟨873149428479083436327973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1164199237972111248437297 873149428479083436327973)
          ·
            refine ⟨163715517839828144311495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 873149428479083436327973 163715517839828144311495)
            ·
              refine ⟨245573276759742216467243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163715517839828144311495 245573276759742216467243)
              ·
                refine ⟨368359915139613324700865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 245573276759742216467243 368359915139613324700865)
                ·
                  refine ⟨276269936354709993525649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 368359915139613324700865 276269936354709993525649)
                  ·
                    refine ⟨207202452266032495144237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 276269936354709993525649 207202452266032495144237)
                    ·
                      refine ⟨77700919599762185679089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 207202452266032495144237 77700919599762185679089)
                      ·
                        rfl

theorem cell23_151322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_151322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151322 prefixEnd_151322 := by exact prefixLift 151322
  have htrace : WordTrace (prefixWord ++ tailWord_151322) baseStart_151322 baseEnd_151322 := by
    simpa [prefixWord, tailWord_151322, baseEnd_151322] using wordTrace_append hprefix tailTrace_151322
  have hstable : (prefixWord ++ tailWord_151322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151322).length < 2 ^ (prefixWord ++ tailWord_151322).sum := by decide
  have hdescent : baseEnd_151322 < baseStart_151322 := by decide
  rcases family_descends (prefixWord ++ tailWord_151322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151352 : List Nat := [2, 1, 2, 1, 3, 4, 2, 1, 3, 1, 3]
def baseStart_151352 : Nat := 118140960795 + 151352 * 2 ^ 59
def prefixEnd_151352 : Nat := 4983230072969 + 3 ^ 40 * 151352 * 2
def baseEnd_151352 : Nat := 77716324019397068303951

theorem tailTrace_151352 : CollatzResearch.WordTrace tailWord_151352 prefixEnd_151352 77716324019397068303951 := by
  unfold tailWord_151352
  simp only [CollatzResearch.WordTrace]
  refine ⟨2760130473842513854388155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3680173965123351805850873 2760130473842513854388155)
  ·
    refine ⟨4140195710763770781582233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2760130473842513854388155 4140195710763770781582233)
    ·
      refine ⟨3105146783072828086186675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4140195710763770781582233 3105146783072828086186675)
      ·
        refine ⟨4657720174609242129280013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3105146783072828086186675 4657720174609242129280013)
        ·
          refine ⟨1746645065478465798480005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4657720174609242129280013 1746645065478465798480005)
          ·
            refine ⟨327495949777212337215001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1746645065478465798480005 327495949777212337215001)
            ·
              refine ⟨245621962332909252911251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 327495949777212337215001 245621962332909252911251)
              ·
                refine ⟨368432943499363879366877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 245621962332909252911251 368432943499363879366877)
                ·
                  refine ⟨138162353812261454762579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 368432943499363879366877 138162353812261454762579)
                  ·
                    refine ⟨207243530718392182143869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 138162353812261454762579 207243530718392182143869)
                    ·
                      refine ⟨77716324019397068303951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 207243530718392182143869 77716324019397068303951)
                      ·
                        rfl

theorem cell23_151352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 3, 1, 3].length) (baseStart_151352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151352 prefixEnd_151352 := by exact prefixLift 151352
  have htrace : WordTrace (prefixWord ++ tailWord_151352) baseStart_151352 baseEnd_151352 := by
    simpa [prefixWord, tailWord_151352, baseEnd_151352] using wordTrace_append hprefix tailTrace_151352
  have hstable : (prefixWord ++ tailWord_151352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151352).length < 2 ^ (prefixWord ++ tailWord_151352).sum := by decide
  have hdescent : baseEnd_151352 < baseStart_151352 := by decide
  rcases family_descends (prefixWord ++ tailWord_151352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151372 : List Nat := [2, 2, 1, 3, 4, 1, 2, 2, 1, 5]
def baseStart_151372 : Nat := 118140960795 + 151372 * 2 ^ 59
def prefixEnd_151372 : Nat := 4983230072969 + 3 ^ 40 * 151372 * 2
def baseEnd_151372 : Nat := 25908864544162330017953

theorem tailTrace_151372 : CollatzResearch.WordTrace tailWord_151372 prefixEnd_151372 25908864544162330017953 := by
  unfold tailWord_151372
  simp only [CollatzResearch.WordTrace]
  refine ⟨2760495203806285562252185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3680660271741714083002913 2760495203806285562252185)
  ·
    refine ⟨2070371402854714171689139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2760495203806285562252185 2070371402854714171689139)
    ·
      refine ⟨3105557104282071257533709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2070371402854714171689139 3105557104282071257533709)
      ·
        refine ⟨1164583914105776721575141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3105557104282071257533709 1164583914105776721575141)
        ·
          refine ⟨218359483894833135295339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1164583914105776721575141 218359483894833135295339)
          ·
            refine ⟨327539225842249702943009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218359483894833135295339 327539225842249702943009)
            ·
              refine ⟨245654419381687277207257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 327539225842249702943009 245654419381687277207257)
              ·
                refine ⟨184240814536265457905443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 245654419381687277207257 184240814536265457905443)
                ·
                  refine ⟨276361221804398186858165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 184240814536265457905443 276361221804398186858165)
                  ·
                    refine ⟨25908864544162330017953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 276361221804398186858165 25908864544162330017953)
                    ·
                      rfl

theorem cell23_151372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 2, 1, 5].length) (baseStart_151372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151372 prefixEnd_151372 := by exact prefixLift 151372
  have htrace : WordTrace (prefixWord ++ tailWord_151372) baseStart_151372 baseEnd_151372 := by
    simpa [prefixWord, tailWord_151372, baseEnd_151372] using wordTrace_append hprefix tailTrace_151372
  have hstable : (prefixWord ++ tailWord_151372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151372).length < 2 ^ (prefixWord ++ tailWord_151372).sum := by decide
  have hdescent : baseEnd_151372 < baseStart_151372 := by decide
  rcases family_descends (prefixWord ++ tailWord_151372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151422 : List Nat := [4, 2, 3, 1, 1, 1, 2, 1, 1, 1, 6]
def baseStart_151422 : Nat := 118140960795 + 151422 * 2 ^ 59
def prefixEnd_151422 : Nat := 4983230072969 + 3 ^ 40 * 151422 * 2
def baseEnd_151422 : Nat := 77752267665211794428629

theorem tailTrace_151422 : CollatzResearch.WordTrace tailWord_151422 prefixEnd_151422 77752267665211794428629 := by
  unfold tailWord_151422
  simp only [CollatzResearch.WordTrace]
  refine ⟨690351757178928707978065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3681876038287619775883013 690351757178928707978065)
  ·
    refine ⟨517763817884196530983549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 690351757178928707978065 517763817884196530983549)
    ·
      refine ⟨194161431706573699118831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 517763817884196530983549 194161431706573699118831)
      ·
        refine ⟨291242147559860548678247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194161431706573699118831 291242147559860548678247)
        ·
          refine ⟨436863221339790823017371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291242147559860548678247 436863221339790823017371)
          ·
            refine ⟨655294832009686234526057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 436863221339790823017371 655294832009686234526057)
            ·
              refine ⟨491471124007264675894543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 655294832009686234526057 491471124007264675894543)
              ·
                refine ⟨737206686010897013841815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 491471124007264675894543 737206686010897013841815)
                ·
                  refine ⟨1105810029016345520762723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 737206686010897013841815 1105810029016345520762723)
                  ·
                    refine ⟨1658715043524518281144085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1105810029016345520762723 1658715043524518281144085)
                    ·
                      refine ⟨77752267665211794428629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1658715043524518281144085 77752267665211794428629)
                      ·
                        rfl

theorem cell23_151422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_151422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151422 prefixEnd_151422 := by exact prefixLift 151422
  have htrace : WordTrace (prefixWord ++ tailWord_151422) baseStart_151422 baseEnd_151422 := by
    simpa [prefixWord, tailWord_151422, baseEnd_151422] using wordTrace_append hprefix tailTrace_151422
  have hstable : (prefixWord ++ tailWord_151422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151422).length < 2 ^ (prefixWord ++ tailWord_151422).sum := by decide
  have hdescent : baseEnd_151422 < baseStart_151422 := by decide
  rcases family_descends (prefixWord ++ tailWord_151422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151442 : List Nat := [3, 2, 3, 2, 1, 1, 1, 1, 3, 3, 3]
def baseStart_151442 : Nat := 118140960795 + 151442 * 2 ^ 59
def prefixEnd_151442 : Nat := 4983230072969 + 3 ^ 40 * 151442 * 2
def baseEnd_151442 : Nat := 77762537278301716178537

theorem tailTrace_151442 : CollatzResearch.WordTrace tailWord_151442 prefixEnd_151442 77762537278301716178537 := by
  unfold tailWord_151442
  simp only [CollatzResearch.WordTrace]
  refine ⟨1380885879339743269888145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3682362344905982053035053 1380885879339743269888145)
  ·
    refine ⟨1035664409504807452416109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1380885879339743269888145 1035664409504807452416109)
    ·
      refine ⟨388374153564302794656041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1035664409504807452416109 388374153564302794656041)
      ·
        refine ⟨291280615173227095992031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 388374153564302794656041 291280615173227095992031)
        ·
          refine ⟨436920922759840643988047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291280615173227095992031 436920922759840643988047)
          ·
            refine ⟨655381384139760965982071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 436920922759840643988047 655381384139760965982071)
            ·
              refine ⟨983072076209641448973107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 655381384139760965982071 983072076209641448973107)
              ·
                refine ⟨1474608114314462173459661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 983072076209641448973107 1474608114314462173459661)
                ·
                  refine ⟨552978042867923315047373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1474608114314462173459661 552978042867923315047373)
                  ·
                    refine ⟨207366766075471243142765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 552978042867923315047373 207366766075471243142765)
                    ·
                      refine ⟨77762537278301716178537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 207366766075471243142765 77762537278301716178537)
                      ·
                        rfl

theorem cell23_151442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_151442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151442 prefixEnd_151442 := by exact prefixLift 151442
  have htrace : WordTrace (prefixWord ++ tailWord_151442) baseStart_151442 baseEnd_151442 := by
    simpa [prefixWord, tailWord_151442, baseEnd_151442] using wordTrace_append hprefix tailTrace_151442
  have hstable : (prefixWord ++ tailWord_151442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151442).length < 2 ^ (prefixWord ++ tailWord_151442).sum := by decide
  have hdescent : baseEnd_151442 < baseStart_151442 := by decide
  rcases family_descends (prefixWord ++ tailWord_151442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151476 : List Nat := [2, 5, 2, 1, 2, 1, 2, 1, 1, 3, 3]
def baseStart_151476 : Nat := 118140960795 + 151476 * 2 ^ 59
def prefixEnd_151476 : Nat := 4983230072969 + 3 ^ 40 * 151476 * 2
def baseEnd_151476 : Nat := 77779995620554583153381

theorem tailTrace_151476 : CollatzResearch.WordTrace tailWord_151476 prefixEnd_151476 77779995620554583153381 := by
  unfold tailWord_151476
  simp only [CollatzResearch.WordTrace]
  refine ⟨2762391799617898443145141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3683189066157197924193521 2762391799617898443145141)
  ·
    refine ⟨258974231214177979044857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2762391799617898443145141 258974231214177979044857)
    ·
      refine ⟨194230673410633484283643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258974231214177979044857 194230673410633484283643)
      ·
        refine ⟨291346010115950226425465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194230673410633484283643 291346010115950226425465)
        ·
          refine ⟨218509507586962669819099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 291346010115950226425465 218509507586962669819099)
          ·
            refine ⟨327764261380444004728649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218509507586962669819099 327764261380444004728649)
            ·
              refine ⟨245823196035333003546487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 327764261380444004728649 245823196035333003546487)
              ·
                refine ⟨368734794052999505319731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 245823196035333003546487 368734794052999505319731)
                ·
                  refine ⟨553102191079499257979597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 368734794052999505319731 553102191079499257979597)
                  ·
                    refine ⟨207413321654812221742349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 553102191079499257979597 207413321654812221742349)
                    ·
                      refine ⟨77779995620554583153381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 207413321654812221742349 77779995620554583153381)
                      ·
                        rfl

theorem cell23_151476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_151476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151476 prefixEnd_151476 := by exact prefixLift 151476
  have htrace : WordTrace (prefixWord ++ tailWord_151476) baseStart_151476 baseEnd_151476 := by
    simpa [prefixWord, tailWord_151476, baseEnd_151476] using wordTrace_append hprefix tailTrace_151476
  have hstable : (prefixWord ++ tailWord_151476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151476).length < 2 ^ (prefixWord ++ tailWord_151476).sum := by decide
  have hdescent : baseEnd_151476 < baseStart_151476 := by decide
  rcases family_descends (prefixWord ++ tailWord_151476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151510 : List Nat := [5, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3]
def baseStart_151510 : Nat := 118140960795 + 151510 * 2 ^ 59
def prefixEnd_151510 : Nat := 4983230072969 + 3 ^ 40 * 151510 * 2
def baseEnd_151510 : Nat := 77797453962807450128225

theorem tailTrace_151510 : CollatzResearch.WordTrace tailWord_151510 prefixEnd_151510 77797453962807450128225 := by
  unfold tailWord_151510
  simp only [CollatzResearch.WordTrace]
  refine ⟨345376480069538793314249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3684015787408413795351989 345376480069538793314249)
  ·
    refine ⟨259032360052154094985687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 345376480069538793314249 259032360052154094985687)
    ·
      refine ⟨388548540078231142478531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259032360052154094985687 388548540078231142478531)
      ·
        refine ⟨582822810117346713717797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388548540078231142478531 582822810117346713717797)
        ·
          refine ⟨109279276897002508822087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 582822810117346713717797 109279276897002508822087)
          ·
            refine ⟨163918915345503763233131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109279276897002508822087 163918915345503763233131)
            ·
              refine ⟨245878373018255644849697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163918915345503763233131 245878373018255644849697)
              ·
                refine ⟨184408779763691733637273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 245878373018255644849697 184408779763691733637273)
                ·
                  refine ⟨138306584822768800227955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 184408779763691733637273 138306584822768800227955)
                  ·
                    refine ⟨207459877234153200341933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 138306584822768800227955 207459877234153200341933)
                    ·
                      refine ⟨77797453962807450128225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 207459877234153200341933 77797453962807450128225)
                      ·
                        rfl

theorem cell23_151510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_151510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151510 prefixEnd_151510 := by exact prefixLift 151510
  have htrace : WordTrace (prefixWord ++ tailWord_151510) baseStart_151510 baseEnd_151510 := by
    simpa [prefixWord, tailWord_151510, baseEnd_151510] using wordTrace_append hprefix tailTrace_151510
  have hstable : (prefixWord ++ tailWord_151510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151510).length < 2 ^ (prefixWord ++ tailWord_151510).sum := by decide
  have hdescent : baseEnd_151510 < baseStart_151510 := by decide
  rcases family_descends (prefixWord ++ tailWord_151510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151533 : List Nat := [1, 5, 1, 4, 1, 2, 1, 1, 1, 4, 2]
def baseStart_151533 : Nat := 118140960795 + 151533 * 2 ^ 59
def prefixEnd_151533 : Nat := 4983230072969 + 3 ^ 40 * 151533 * 2
def baseEnd_151533 : Nat := 77809264017860860140619

theorem tailTrace_151533 : CollatzResearch.WordTrace tailWord_151533 prefixEnd_151533 77809264017860860140619 := by
  unfold tailWord_151533
  simp only [CollatzResearch.WordTrace]
  refine ⟨5526862560029295621115253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3684575040019530414076835 5526862560029295621115253)
  ·
    refine ⟨518143365002746464479555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5526862560029295621115253 518143365002746464479555)
    ·
      refine ⟨777215047504119696719333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 518143365002746464479555 777215047504119696719333)
      ·
        refine ⟨145727821407022443134875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 777215047504119696719333 145727821407022443134875)
        ·
          refine ⟨218591732110533664702313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145727821407022443134875 218591732110533664702313)
          ·
            refine ⟨163943799082900248526735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 218591732110533664702313 163943799082900248526735)
            ·
              refine ⟨245915698624350372790103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163943799082900248526735 245915698624350372790103)
              ·
                refine ⟨368873547936525559185155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 245915698624350372790103 368873547936525559185155)
                ·
                  refine ⟨553310321904788338777733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 368873547936525559185155 553310321904788338777733)
                  ·
                    refine ⟨103745685357147813520825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 553310321904788338777733 103745685357147813520825)
                    ·
                      refine ⟨77809264017860860140619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 103745685357147813520825 77809264017860860140619)
                      ·
                        rfl

theorem cell23_151533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_151533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151533 prefixEnd_151533 := by exact prefixLift 151533
  have htrace : WordTrace (prefixWord ++ tailWord_151533) baseStart_151533 baseEnd_151533 := by
    simpa [prefixWord, tailWord_151533, baseEnd_151533] using wordTrace_append hprefix tailTrace_151533
  have hstable : (prefixWord ++ tailWord_151533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151533).length < 2 ^ (prefixWord ++ tailWord_151533).sum := by decide
  have hdescent : baseEnd_151533 < baseStart_151533 := by decide
  rcases family_descends (prefixWord ++ tailWord_151533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151555 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 6, 1, 4]
def baseStart_151555 : Nat := 118140960795 + 151555 * 2 ^ 59
def prefixEnd_151555 : Nat := 4983230072969 + 3 ^ 40 * 151555 * 2
def baseEnd_151555 : Nat := 77820560592259774065517

theorem tailTrace_151555 : CollatzResearch.WordTrace tailWord_151555 prefixEnd_151555 77820560592259774065517 := by
  unfold tailWord_151555
  simp only [CollatzResearch.WordTrace]
  refine ⟨5527664965949593378416119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3685109977299728918944079 5527664965949593378416119)
  ·
    refine ⟨8291497448924390067624179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5527664965949593378416119 8291497448924390067624179)
    ·
      refine ⟨12437246173386585101436269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8291497448924390067624179 12437246173386585101436269)
      ·
        refine ⟨4663967315019969413038601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12437246173386585101436269 4663967315019969413038601)
        ·
          refine ⟨3497975486264977059778951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4663967315019969413038601 3497975486264977059778951)
          ·
            refine ⟨5246963229397465589668427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3497975486264977059778951 5246963229397465589668427)
            ·
              refine ⟨7870444844096198384502641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5246963229397465589668427 7870444844096198384502641)
              ·
                refine ⟨5902833633072148788376981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7870444844096198384502641 5902833633072148788376981)
                ·
                  refine ⟨276695326550256974455171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5902833633072148788376981 276695326550256974455171)
                  ·
                    refine ⟨415042989825385461682757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 276695326550256974455171 415042989825385461682757)
                    ·
                      refine ⟨77820560592259774065517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 415042989825385461682757 77820560592259774065517)
                      ·
                        rfl

theorem cell23_151555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 6, 1, 4].length) (baseStart_151555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151555 prefixEnd_151555 := by exact prefixLift 151555
  have htrace : WordTrace (prefixWord ++ tailWord_151555) baseStart_151555 baseEnd_151555 := by
    simpa [prefixWord, tailWord_151555, baseEnd_151555] using wordTrace_append hprefix tailTrace_151555
  have hstable : (prefixWord ++ tailWord_151555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151555).length < 2 ^ (prefixWord ++ tailWord_151555).sum := by decide
  have hdescent : baseEnd_151555 < baseStart_151555 := by decide
  rcases family_descends (prefixWord ++ tailWord_151555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151629 : List Nat := [1, 6, 1, 1, 1, 1, 4, 2, 6]
def baseStart_151629 : Nat := 118140960795 + 151629 * 2 ^ 59
def prefixEnd_151629 : Nat := 4983230072969 + 3 ^ 40 * 151629 * 2
def baseEnd_151629 : Nat := 8650950906743609393353

theorem tailTrace_151629 : CollatzResearch.WordTrace tailWord_151629 prefixEnd_151629 8650950906743609393353 := by
  unfold tailWord_151629
  simp only [CollatzResearch.WordTrace]
  refine ⟨5530363967681504016609941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3686909311787669344406627 5530363967681504016609941)
  ·
    refine ⟨259235810985070500778591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5530363967681504016609941 259235810985070500778591)
    ·
      refine ⟨388853716477605751167887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259235810985070500778591 388853716477605751167887)
      ·
        refine ⟨583280574716408626751831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388853716477605751167887 583280574716408626751831)
        ·
          refine ⟨874920862074612940127747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 583280574716408626751831 874920862074612940127747)
          ·
            refine ⟨1312381293111919410191621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 874920862074612940127747 1312381293111919410191621)
            ·
              refine ⟨246071492458484889410929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1312381293111919410191621 246071492458484889410929)
              ·
                refine ⟨184553619343863667058197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 246071492458484889410929 184553619343863667058197)
                ·
                  refine ⟨8650950906743609393353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 184553619343863667058197 8650950906743609393353)
                  ·
                    rfl

theorem cell23_151629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_151629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151629 prefixEnd_151629 := by exact prefixLift 151629
  have htrace : WordTrace (prefixWord ++ tailWord_151629) baseStart_151629 baseEnd_151629 := by
    simpa [prefixWord, tailWord_151629, baseEnd_151629] using wordTrace_append hprefix tailTrace_151629
  have hstable : (prefixWord ++ tailWord_151629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151629).length < 2 ^ (prefixWord ++ tailWord_151629).sum := by decide
  have hdescent : baseEnd_151629 < baseStart_151629 := by decide
  rcases family_descends (prefixWord ++ tailWord_151629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151632 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 5, 5, 2]
def baseStart_151632 : Nat := 118140960795 + 151632 * 2 ^ 59
def prefixEnd_151632 : Nat := 4983230072969 + 3 ^ 40 * 151632 * 2
def baseEnd_151632 : Nat := 77860098602655972802663

theorem tailTrace_151632 : CollatzResearch.WordTrace tailWord_151632 prefixEnd_151632 77860098602655972802663 := by
  unfold tailWord_151632
  simp only [CollatzResearch.WordTrace]
  refine ⟨2765236693335317764484575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3686982257780423685979433 2765236693335317764484575)
  ·
    refine ⟨4147855040002976646726863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2765236693335317764484575 4147855040002976646726863)
    ·
      refine ⟨6221782560004464970090295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4147855040002976646726863 6221782560004464970090295)
      ·
        refine ⟨9332673840006697455135443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6221782560004464970090295 9332673840006697455135443)
        ·
          refine ⟨13999010760010046182703165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9332673840006697455135443 13999010760010046182703165)
          ·
            refine ⟨5249629035003767318513687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13999010760010046182703165 5249629035003767318513687)
            ·
              refine ⟨7874443552505650977770531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5249629035003767318513687 7874443552505650977770531)
              ·
                refine ⟨11811665328758476466655797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7874443552505650977770531 11811665328758476466655797)
                ·
                  refine ⟨1107343624571107168748981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11811665328758476466655797 1107343624571107168748981)
                  ·
                    refine ⟨103813464803541297070217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1107343624571107168748981 103813464803541297070217)
                    ·
                      refine ⟨77860098602655972802663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 103813464803541297070217 77860098602655972802663)
                      ·
                        rfl

theorem cell23_151632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 5, 5, 2].length) (baseStart_151632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151632 prefixEnd_151632 := by exact prefixLift 151632
  have htrace : WordTrace (prefixWord ++ tailWord_151632) baseStart_151632 baseEnd_151632 := by
    simpa [prefixWord, tailWord_151632, baseEnd_151632] using wordTrace_append hprefix tailTrace_151632
  have hstable : (prefixWord ++ tailWord_151632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151632).length < 2 ^ (prefixWord ++ tailWord_151632).sum := by decide
  have hdescent : baseEnd_151632 < baseStart_151632 := by decide
  rcases family_descends (prefixWord ++ tailWord_151632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151666 : List Nat := [3, 2, 1, 2, 2, 2, 3, 1, 2, 3, 2]
def baseStart_151666 : Nat := 118140960795 + 151666 * 2 ^ 59
def prefixEnd_151666 : Nat := 4983230072969 + 3 ^ 40 * 151666 * 2
def baseEnd_151666 : Nat := 77877556944908839777507

theorem tailTrace_151666 : CollatzResearch.WordTrace tailWord_151666 prefixEnd_151666 77877556944908839777507 := by
  unfold tailWord_151666
  simp only [CollatzResearch.WordTrace]
  refine ⟨1382928367136864833926713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3687808979031639557137901 1382928367136864833926713)
  ·
    refine ⟨1037196275352648625445035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1382928367136864833926713 1037196275352648625445035)
    ·
      refine ⟨1555794413028972938167553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1037196275352648625445035 1555794413028972938167553)
      ·
        refine ⟨1166845809771729703625665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1555794413028972938167553 1166845809771729703625665)
        ·
          refine ⟨875134357328797277719249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1166845809771729703625665 875134357328797277719249)
          ·
            refine ⟨656350767996597958289437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 875134357328797277719249 656350767996597958289437)
            ·
              refine ⟨246131537998724234358539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 656350767996597958289437 246131537998724234358539)
              ·
                refine ⟨369197306998086351537809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 246131537998724234358539 369197306998086351537809)
                ·
                  refine ⟨276897980248564763653357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 369197306998086351537809 276897980248564763653357)
                  ·
                    refine ⟨103836742593211786370009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 276897980248564763653357 103836742593211786370009)
                    ·
                      refine ⟨77877556944908839777507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 103836742593211786370009 77877556944908839777507)
                      ·
                        rfl

theorem cell23_151666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 2, 3, 2].length) (baseStart_151666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151666 prefixEnd_151666 := by exact prefixLift 151666
  have htrace : WordTrace (prefixWord ++ tailWord_151666) baseStart_151666 baseEnd_151666 := by
    simpa [prefixWord, tailWord_151666, baseEnd_151666] using wordTrace_append hprefix tailTrace_151666
  have hstable : (prefixWord ++ tailWord_151666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151666).length < 2 ^ (prefixWord ++ tailWord_151666).sum := by decide
  have hdescent : baseEnd_151666 < baseStart_151666 := by decide
  rcases family_descends (prefixWord ++ tailWord_151666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151672 : List Nat := [2, 1, 2, 1, 1, 1, 3, 4, 4, 4]
def baseStart_151672 : Nat := 118140960795 + 151672 * 2 ^ 59
def prefixEnd_151672 : Nat := 4983230072969 + 3 ^ 40 * 151672 * 2
def baseEnd_151672 : Nat := 25960212609611938767493

theorem tailTrace_151672 : CollatzResearch.WordTrace tailWord_151672 prefixEnd_151672 25960212609611938767493 := by
  unfold tailWord_151672
  simp only [CollatzResearch.WordTrace]
  refine ⟨2765966153262861180212635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3687954871017148240283513 2765966153262861180212635)
  ·
    refine ⟨4148949229894291770318953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2765966153262861180212635 4148949229894291770318953)
    ·
      refine ⟨3111711922420718827739215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4148949229894291770318953 3111711922420718827739215)
      ·
        refine ⟨4667567883631078241608823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3111711922420718827739215 4667567883631078241608823)
        ·
          refine ⟨7001351825446617362413235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4667567883631078241608823 7001351825446617362413235)
          ·
            refine ⟨10502027738169926043619853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7001351825446617362413235 10502027738169926043619853)
            ·
              refine ⟨3938260401813722266357445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10502027738169926043619853 3938260401813722266357445)
              ·
                refine ⟨738423825340072924942021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3938260401813722266357445 738423825340072924942021)
                ·
                  refine ⟨138454467251263673426629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 738423825340072924942021 138454467251263673426629)
                  ·
                    refine ⟨25960212609611938767493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 138454467251263673426629 25960212609611938767493)
                    ·
                      rfl

theorem cell23_151672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 4, 4].length) (baseStart_151672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151672 prefixEnd_151672 := by exact prefixLift 151672
  have htrace : WordTrace (prefixWord ++ tailWord_151672) baseStart_151672 baseEnd_151672 := by
    simpa [prefixWord, tailWord_151672, baseEnd_151672] using wordTrace_append hprefix tailTrace_151672
  have hstable : (prefixWord ++ tailWord_151672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151672).length < 2 ^ (prefixWord ++ tailWord_151672).sum := by decide
  have hdescent : baseEnd_151672 < baseStart_151672 := by decide
  rcases family_descends (prefixWord ++ tailWord_151672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151673 : List Nat := [1, 2, 1, 3, 4, 2, 2, 3, 1, 1, 3]
def baseStart_151673 : Nat := 118140960795 + 151673 * 2 ^ 59
def prefixEnd_151673 : Nat := 4983230072969 + 3 ^ 40 * 151673 * 2
def baseEnd_151673 : Nat := 77881151309490312389975

theorem tailTrace_151673 : CollatzResearch.WordTrace tailWord_151673 prefixEnd_151673 77881151309490312389975 := by
  unfold tailWord_151673
  simp only [CollatzResearch.WordTrace]
  refine ⟨5531968779522099531211673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3687979186348066354141115 5531968779522099531211673)
  ·
    refine ⟨4148976584641574648408755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5531968779522099531211673 4148976584641574648408755)
    ·
      refine ⟨6223464876962361972613133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4148976584641574648408755 6223464876962361972613133)
      ·
        refine ⟨2333799328860885739729925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6223464876962361972613133 2333799328860885739729925)
        ·
          refine ⟨437587374161416076199361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2333799328860885739729925 437587374161416076199361)
          ·
            refine ⟨328190530621062057149521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 437587374161416076199361 328190530621062057149521)
            ·
              refine ⟨246142897965796542862141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 328190530621062057149521 246142897965796542862141)
              ·
                refine ⟨92303586737173703573303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 246142897965796542862141 92303586737173703573303)
                ·
                  refine ⟨138455380105760555359955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92303586737173703573303 138455380105760555359955)
                  ·
                    refine ⟨207683070158640833039933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 138455380105760555359955 207683070158640833039933)
                    ·
                      refine ⟨77881151309490312389975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 207683070158640833039933 77881151309490312389975)
                      ·
                        rfl

theorem cell23_151673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 3, 1, 1, 3].length) (baseStart_151673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151673 prefixEnd_151673 := by exact prefixLift 151673
  have htrace : WordTrace (prefixWord ++ tailWord_151673) baseStart_151673 baseEnd_151673 := by
    simpa [prefixWord, tailWord_151673, baseEnd_151673] using wordTrace_append hprefix tailTrace_151673
  have hstable : (prefixWord ++ tailWord_151673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151673).length < 2 ^ (prefixWord ++ tailWord_151673).sum := by decide
  have hdescent : baseEnd_151673 < baseStart_151673 := by decide
  rcases family_descends (prefixWord ++ tailWord_151673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151675 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 6]
def baseStart_151675 : Nat := 118140960795 + 151675 * 2 ^ 59
def prefixEnd_151675 : Nat := 4983230072969 + 3 ^ 40 * 151675 * 2
def baseEnd_151675 : Nat := 77882178270799304564965

theorem tailTrace_151675 : CollatzResearch.WordTrace tailWord_151675 prefixEnd_151675 77882178270799304564965 := by
  unfold tailWord_151675
  simp only [CollatzResearch.WordTrace]
  refine ⟨5532041725514853872784479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3688027817009902581856319 5532041725514853872784479)
  ·
    refine ⟨8298062588272280809176719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5532041725514853872784479 8298062588272280809176719)
    ·
      refine ⟨12447093882408421213765079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8298062588272280809176719 12447093882408421213765079)
      ·
        refine ⟨18670640823612631820647619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12447093882408421213765079 18670640823612631820647619)
        ·
          refine ⟨28005961235418947730971429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18670640823612631820647619 28005961235418947730971429)
          ·
            refine ⟨5251117731641052699557143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28005961235418947730971429 5251117731641052699557143)
            ·
              refine ⟨7876676597461579049335715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5251117731641052699557143 7876676597461579049335715)
              ·
                refine ⟨11815014896192368574003573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7876676597461579049335715 11815014896192368574003573)
                ·
                  refine ⟨1107657646518034553812835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11815014896192368574003573 1107657646518034553812835)
                  ·
                    refine ⟨1661486469777051830719253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1107657646518034553812835 1661486469777051830719253)
                    ·
                      refine ⟨77882178270799304564965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1661486469777051830719253 77882178270799304564965)
                      ·
                        rfl

theorem cell23_151675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 6].length) (baseStart_151675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151675 prefixEnd_151675 := by exact prefixLift 151675
  have htrace : WordTrace (prefixWord ++ tailWord_151675) baseStart_151675 baseEnd_151675 := by
    simpa [prefixWord, tailWord_151675, baseEnd_151675] using wordTrace_append hprefix tailTrace_151675
  have hstable : (prefixWord ++ tailWord_151675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151675).length < 2 ^ (prefixWord ++ tailWord_151675).sum := by decide
  have hdescent : baseEnd_151675 < baseStart_151675 := by decide
  rcases family_descends (prefixWord ++ tailWord_151675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151676 : List Nat := [2, 2, 2, 1, 1, 6, 2, 1, 1, 5]
def baseStart_151676 : Nat := 118140960795 + 151676 * 2 ^ 59
def prefixEnd_151676 : Nat := 4983230072969 + 3 ^ 40 * 151676 * 2
def baseEnd_151676 : Nat := 25960897250484600217487

theorem tailTrace_151676 : CollatzResearch.WordTrace tailWord_151676 prefixEnd_151676 25960897250484600217487 := by
  unfold tailWord_151676
  simp only [CollatzResearch.WordTrace]
  refine ⟨2766039099255615521785441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3688052132340820695713921 2766039099255615521785441)
  ·
    refine ⟨2074529324441711641339081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2766039099255615521785441 2074529324441711641339081)
    ·
      refine ⟨1555896993331283731004311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2074529324441711641339081 1555896993331283731004311)
      ·
        refine ⟨2333845489996925596506467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1555896993331283731004311 2333845489996925596506467)
        ·
          refine ⟨3500768234995388394759701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2333845489996925596506467 3500768234995388394759701)
          ·
            refine ⟨164098511015408831004361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3500768234995388394759701 164098511015408831004361)
            ·
              refine ⟨123073883261556623253271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164098511015408831004361 123073883261556623253271)
              ·
                refine ⟨184610824892334934879907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123073883261556623253271 184610824892334934879907)
                ·
                  refine ⟨276916237338502402319861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 184610824892334934879907 276916237338502402319861)
                  ·
                    refine ⟨25960897250484600217487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 276916237338502402319861 25960897250484600217487)
                    ·
                      rfl

theorem cell23_151676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 1, 1, 5].length) (baseStart_151676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151676 prefixEnd_151676 := by exact prefixLift 151676
  have htrace : WordTrace (prefixWord ++ tailWord_151676) baseStart_151676 baseEnd_151676 := by
    simpa [prefixWord, tailWord_151676, baseEnd_151676] using wordTrace_append hprefix tailTrace_151676
  have hstable : (prefixWord ++ tailWord_151676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151676).length < 2 ^ (prefixWord ++ tailWord_151676).sum := by decide
  have hdescent : baseEnd_151676 < baseStart_151676 := by decide
  rcases family_descends (prefixWord ++ tailWord_151676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151696 : List Nat := [2, 1, 1, 1, 1, 1, 8, 1, 3, 2, 2]
def baseStart_151696 : Nat := 118140960795 + 151696 * 2 ^ 59
def prefixEnd_151696 : Nat := 4983230072969 + 3 ^ 40 * 151696 * 2
def baseEnd_151696 : Nat := 77892961364543722402369

theorem tailTrace_151696 : CollatzResearch.WordTrace tailWord_151696 prefixEnd_151696 77892961364543722402369 := by
  unfold tailWord_151696
  simp only [CollatzResearch.WordTrace]
  refine ⟨2766403829219387229649471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3688538438959182972865961 2766403829219387229649471)
  ·
    refine ⟨4149605743829080844474207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2766403829219387229649471 4149605743829080844474207)
    ·
      refine ⟨6224408615743621266711311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4149605743829080844474207 6224408615743621266711311)
      ·
        refine ⟨9336612923615431900066967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6224408615743621266711311 9336612923615431900066967)
        ·
          refine ⟨14004919385423147850100451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9336612923615431900066967 14004919385423147850100451)
          ·
            refine ⟨21007379078134721775150677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14004919385423147850100451 21007379078134721775150677)
            ·
              refine ⟨246180223571891270802547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 21007379078134721775150677 246180223571891270802547)
              ·
                refine ⟨369270335357836906203821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 246180223571891270802547 369270335357836906203821)
                ·
                  refine ⟨138476375759188839826433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 369270335357836906203821 138476375759188839826433)
                  ·
                    refine ⟨103857281819391629869825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 138476375759188839826433 103857281819391629869825)
                    ·
                      refine ⟨77892961364543722402369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 103857281819391629869825 77892961364543722402369)
                      ·
                        rfl

theorem cell23_151696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 3, 2, 2].length) (baseStart_151696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151696 prefixEnd_151696 := by exact prefixLift 151696
  have htrace : WordTrace (prefixWord ++ tailWord_151696) baseStart_151696 baseEnd_151696 := by
    simpa [prefixWord, tailWord_151696, baseEnd_151696] using wordTrace_append hprefix tailTrace_151696
  have hstable : (prefixWord ++ tailWord_151696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151696).length < 2 ^ (prefixWord ++ tailWord_151696).sum := by decide
  have hdescent : baseEnd_151696 < baseStart_151696 := by decide
  rcases family_descends (prefixWord ++ tailWord_151696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151706 : List Nat := [3, 1, 1, 5, 2, 2, 1, 1, 1, 6]
def baseStart_151706 : Nat := 118140960795 + 151706 * 2 ^ 59
def prefixEnd_151706 : Nat := 4983230072969 + 3 ^ 40 * 151706 * 2
def baseEnd_151706 : Nat := 25966032057029561092441

theorem tailTrace_151706 : CollatzResearch.WordTrace tailWord_151706 prefixEnd_151706 25966032057029561092441 := by
  unfold tailWord_151706
  simp only [CollatzResearch.WordTrace]
  refine ⟨1383293097100636541790743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3688781592268364111441981 1383293097100636541790743)
  ·
    refine ⟨2074939645650954812686115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1383293097100636541790743 2074939645650954812686115)
    ·
      refine ⟨3112409468476432219029173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2074939645650954812686115 3112409468476432219029173)
      ·
        refine ⟨291788387669665520533985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3112409468476432219029173 291788387669665520533985)
        ·
          refine ⟨218841290752249140400489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 291788387669665520533985 218841290752249140400489)
          ·
            refine ⟨164130968064186855300367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 218841290752249140400489 164130968064186855300367)
            ·
              refine ⟨246196452096280282950551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164130968064186855300367 246196452096280282950551)
              ·
                refine ⟨369294678144420424425827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 246196452096280282950551 369294678144420424425827)
                ·
                  refine ⟨553942017216630636638741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 369294678144420424425827 553942017216630636638741)
                  ·
                    refine ⟨25966032057029561092441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 553942017216630636638741 25966032057029561092441)
                    ·
                      rfl

theorem cell23_151706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 1, 6].length) (baseStart_151706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151706 prefixEnd_151706 := by exact prefixLift 151706
  have htrace : WordTrace (prefixWord ++ tailWord_151706) baseStart_151706 baseEnd_151706 := by
    simpa [prefixWord, tailWord_151706, baseEnd_151706] using wordTrace_append hprefix tailTrace_151706
  have hstable : (prefixWord ++ tailWord_151706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151706).length < 2 ^ (prefixWord ++ tailWord_151706).sum := by decide
  have hdescent : baseEnd_151706 < baseStart_151706 := by decide
  rcases family_descends (prefixWord ++ tailWord_151706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151709 : List Nat := [1, 4, 2, 1, 1, 3, 3, 1, 1, 2, 4]
def baseStart_151709 : Nat := 118140960795 + 151709 * 2 ^ 59
def prefixEnd_151709 : Nat := 4983230072969 + 3 ^ 40 * 151709 * 2
def baseEnd_151709 : Nat := 77899636613052171539809

theorem tailTrace_151709 : CollatzResearch.WordTrace tailWord_151709 prefixEnd_151709 77899636613052171539809 := by
  unfold tailWord_151709
  simp only [CollatzResearch.WordTrace]
  refine ⟨5533281807391677679522181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3688854538261118453014787 5533281807391677679522181)
  ·
    refine ⟨1037490338885939564910409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5533281807391677679522181 1037490338885939564910409)
    ·
      refine ⟨778117754164454673682807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1037490338885939564910409 778117754164454673682807)
      ·
        refine ⟨1167176631246682010524211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 778117754164454673682807 1167176631246682010524211)
        ·
          refine ⟨1750764946870023015786317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1167176631246682010524211 1750764946870023015786317)
          ·
            refine ⟨656536855076258630919869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1750764946870023015786317 656536855076258630919869)
            ·
              refine ⟨246201320653596986594951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 656536855076258630919869 246201320653596986594951)
              ·
                refine ⟨369301980980395479892427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 246201320653596986594951 369301980980395479892427)
                ·
                  refine ⟨553952971470593219838641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 369301980980395479892427 553952971470593219838641)
                  ·
                    refine ⟨415464728602944914878981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 553952971470593219838641 415464728602944914878981)
                    ·
                      refine ⟨77899636613052171539809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 415464728602944914878981 77899636613052171539809)
                      ·
                        rfl

theorem cell23_151709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_151709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151709 prefixEnd_151709 := by exact prefixLift 151709
  have htrace : WordTrace (prefixWord ++ tailWord_151709) baseStart_151709 baseEnd_151709 := by
    simpa [prefixWord, tailWord_151709, baseEnd_151709] using wordTrace_append hprefix tailTrace_151709
  have hstable : (prefixWord ++ tailWord_151709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151709).length < 2 ^ (prefixWord ++ tailWord_151709).sum := by decide
  have hdescent : baseEnd_151709 < baseStart_151709 := by decide
  rcases family_descends (prefixWord ++ tailWord_151709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151719 : List Nat := [1, 1, 6, 2, 2, 1, 1, 9]
def baseStart_151719 : Nat := 118140960795 + 151719 * 2 ^ 59
def prefixEnd_151719 : Nat := 4983230072969 + 3 ^ 40 * 151719 * 2
def baseEnd_151719 : Nat := 2885361904429523422769

theorem tailTrace_151719 : CollatzResearch.WordTrace tailWord_151719 prefixEnd_151719 2885361904429523422769 := by
  unfold tailWord_151719
  simp only [CollatzResearch.WordTrace]
  refine ⟨5533646537355449387386211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3689097691570299591590807 5533646537355449387386211)
  ·
    refine ⟨8300469806033174081079317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5533646537355449387386211 8300469806033174081079317)
    ·
      refine ⟨389084522157805035050593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8300469806033174081079317 389084522157805035050593)
      ·
        refine ⟨291813391618353776287945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 389084522157805035050593 291813391618353776287945)
        ·
          refine ⟨218860043713765332215959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 291813391618353776287945 218860043713765332215959)
          ·
            refine ⟨328290065570647998323939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218860043713765332215959 328290065570647998323939)
            ·
              refine ⟨492435098355971997485909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 328290065570647998323939 492435098355971997485909)
              ·
                refine ⟨2885361904429523422769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 492435098355971997485909 2885361904429523422769)
                ·
                  rfl

theorem cell23_151719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 9].length) (baseStart_151719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151719 prefixEnd_151719 := by exact prefixLift 151719
  have htrace : WordTrace (prefixWord ++ tailWord_151719) baseStart_151719 baseEnd_151719 := by
    simpa [prefixWord, tailWord_151719, baseEnd_151719] using wordTrace_append hprefix tailTrace_151719
  have hstable : (prefixWord ++ tailWord_151719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151719).length < 2 ^ (prefixWord ++ tailWord_151719).sum := by decide
  have hdescent : baseEnd_151719 < baseStart_151719 := by decide
  rcases family_descends (prefixWord ++ tailWord_151719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151752 : List Nat := [2, 1, 3, 1, 2, 1, 1, 3, 2, 3, 4]
def baseStart_151752 : Nat := 118140960795 + 151752 * 2 ^ 59
def prefixEnd_151752 : Nat := 4983230072969 + 3 ^ 40 * 151752 * 2
def baseEnd_151752 : Nat := 77921716281195503302111

theorem tailTrace_151752 : CollatzResearch.WordTrace tailWord_151752 prefixEnd_151752 77921716281195503302111 := by
  unfold tailWord_151752
  simp only [CollatzResearch.WordTrace]
  refine ⟨2767425073117948011668755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3689900097490597348891673 2767425073117948011668755)
  ·
    refine ⟨4151137609676922017503133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2767425073117948011668755 4151137609676922017503133)
    ·
      refine ⟨1556676603628845756563675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4151137609676922017503133 1556676603628845756563675)
      ·
        refine ⟨2335014905443268634845513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1556676603628845756563675 2335014905443268634845513)
        ·
          refine ⟨1751261179082451476134135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2335014905443268634845513 1751261179082451476134135)
          ·
            refine ⟨2626891768623677214201203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1751261179082451476134135 2626891768623677214201203)
            ·
              refine ⟨3940337652935515821301805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2626891768623677214201203 3940337652935515821301805)
              ·
                refine ⟨1477626619850818432988177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3940337652935515821301805 1477626619850818432988177)
                ·
                  refine ⟨1108219964888113824741133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1477626619850818432988177 1108219964888113824741133)
                  ·
                    refine ⟨415582486833042684277925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1108219964888113824741133 415582486833042684277925)
                    ·
                      refine ⟨77921716281195503302111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 415582486833042684277925 77921716281195503302111)
                      ·
                        rfl

theorem cell23_151752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_151752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151752 prefixEnd_151752 := by exact prefixLift 151752
  have htrace : WordTrace (prefixWord ++ tailWord_151752) baseStart_151752 baseEnd_151752 := by
    simpa [prefixWord, tailWord_151752, baseEnd_151752] using wordTrace_append hprefix tailTrace_151752
  have hstable : (prefixWord ++ tailWord_151752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151752).length < 2 ^ (prefixWord ++ tailWord_151752).sum := by decide
  have hdescent : baseEnd_151752 < baseStart_151752 := by decide
  rcases family_descends (prefixWord ++ tailWord_151752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151773 : List Nat := [1, 4, 3, 2, 1, 2, 1, 1, 3, 3, 2]
def baseStart_151773 : Nat := 118140960795 + 151773 * 2 ^ 59
def prefixEnd_151773 : Nat := 4983230072969 + 3 ^ 40 * 151773 * 2
def baseEnd_151773 : Nat := 77932499374939921139515

theorem tailTrace_151773 : CollatzResearch.WordTrace tailWord_151773 prefixEnd_151773 77932499374939921139515 := by
  unfold tailWord_151773
  simp only [CollatzResearch.WordTrace]
  refine ⟨5535616079159816609851973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3690410719439877739901315 5535616079159816609851973)
  ·
    refine ⟨1037928014842465614347245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5535616079159816609851973 1037928014842465614347245)
    ·
      refine ⟨389223005565924605380217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1037928014842465614347245 389223005565924605380217)
      ·
        refine ⟨291917254174443454035163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 389223005565924605380217 291917254174443454035163)
        ·
          refine ⟨437875881261665181052745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291917254174443454035163 437875881261665181052745)
          ·
            refine ⟨328406910946248885789559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 437875881261665181052745 328406910946248885789559)
            ·
              refine ⟨492610366419373328684339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 328406910946248885789559 492610366419373328684339)
              ·
                refine ⟨738915549629059993026509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 492610366419373328684339 738915549629059993026509)
                ·
                  refine ⟨277093331110897497384941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 738915549629059993026509 277093331110897497384941)
                  ·
                    refine ⟨103909999166586561519353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 277093331110897497384941 103909999166586561519353)
                    ·
                      refine ⟨77932499374939921139515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 103909999166586561519353 77932499374939921139515)
                      ·
                        rfl

theorem cell23_151773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_151773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151773 prefixEnd_151773 := by exact prefixLift 151773
  have htrace : WordTrace (prefixWord ++ tailWord_151773) baseStart_151773 baseEnd_151773 := by
    simpa [prefixWord, tailWord_151773, baseEnd_151773] using wordTrace_append hprefix tailTrace_151773
  have hstable : (prefixWord ++ tailWord_151773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151773).length < 2 ^ (prefixWord ++ tailWord_151773).sum := by decide
  have hdescent : baseEnd_151773 < baseStart_151773 := by decide
  rcases family_descends (prefixWord ++ tailWord_151773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151786 : List Nat := [3, 1, 3, 1, 1, 2, 3, 2, 1, 4, 2]
def baseStart_151786 : Nat := 118140960795 + 151786 * 2 ^ 59
def prefixEnd_151786 : Nat := 4983230072969 + 3 ^ 40 * 151786 * 2
def baseEnd_151786 : Nat := 77939174623448370276955

theorem tailTrace_151786 : CollatzResearch.WordTrace tailWord_151786 prefixEnd_151786 77939174623448370276955 := by
  unfold tailWord_151786
  simp only [CollatzResearch.WordTrace]
  refine ⟨1384022557028179957518803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3690726818741813220050141 1384022557028179957518803)
  ·
    refine ⟨2076033835542269936278205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1384022557028179957518803 2076033835542269936278205)
    ·
      refine ⟨778512688328351226104327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2076033835542269936278205 778512688328351226104327)
      ·
        refine ⟨1167769032492526839156491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 778512688328351226104327 1167769032492526839156491)
        ·
          refine ⟨1751653548738790258734737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1167769032492526839156491 1751653548738790258734737)
          ·
            refine ⟨1313740161554092694051053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1751653548738790258734737 1313740161554092694051053)
            ·
              refine ⟨492652560582784760269145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1313740161554092694051053 492652560582784760269145)
              ·
                refine ⟨369489420437088570201859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 492652560582784760269145 369489420437088570201859)
                ·
                  refine ⟨554234130655632855302789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 369489420437088570201859 554234130655632855302789)
                  ·
                    refine ⟨103918899497931160369273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 554234130655632855302789 103918899497931160369273)
                    ·
                      refine ⟨77939174623448370276955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 103918899497931160369273 77939174623448370276955)
                      ·
                        rfl

theorem cell23_151786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 1, 4, 2].length) (baseStart_151786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151786 prefixEnd_151786 := by exact prefixLift 151786
  have htrace : WordTrace (prefixWord ++ tailWord_151786) baseStart_151786 baseEnd_151786 := by
    simpa [prefixWord, tailWord_151786, baseEnd_151786] using wordTrace_append hprefix tailTrace_151786
  have hstable : (prefixWord ++ tailWord_151786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151786).length < 2 ^ (prefixWord ++ tailWord_151786).sum := by decide
  have hdescent : baseEnd_151786 < baseStart_151786 := by decide
  rcases family_descends (prefixWord ++ tailWord_151786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151819 : List Nat := [1, 1, 1, 1, 5, 2, 3, 1, 2, 3, 3]
def baseStart_151819 : Nat := 118140960795 + 151819 * 2 ^ 59
def prefixEnd_151819 : Nat := 4983230072969 + 3 ^ 40 * 151819 * 2
def baseEnd_151819 : Nat := 77956119485046741164303

theorem tailTrace_151819 : CollatzResearch.WordTrace tailWord_151819 prefixEnd_151819 77956119485046741164303 := by
  unfold tailWord_151819
  simp only [CollatzResearch.WordTrace]
  refine ⟨5537293836993166466026511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3691529224662110977351007 5537293836993166466026511)
  ·
    refine ⟨8305940755489749699039767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5537293836993166466026511 8305940755489749699039767)
    ·
      refine ⟨12458911133234624548559651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8305940755489749699039767 12458911133234624548559651)
      ·
        refine ⟨18688366699851936822839477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12458911133234624548559651 18688366699851936822839477)
        ·
          refine ⟨1752034378111119077141201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18688366699851936822839477 1752034378111119077141201)
          ·
            refine ⟨1314025783583339307855901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1752034378111119077141201 1314025783583339307855901)
            ·
              refine ⟨492759668843752240445963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1314025783583339307855901 492759668843752240445963)
              ·
                refine ⟨739139503265628360668945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 492759668843752240445963 739139503265628360668945)
                ·
                  refine ⟨554354627449221270501709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 739139503265628360668945 554354627449221270501709)
                  ·
                    refine ⟨207882985293457976438141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 554354627449221270501709 207882985293457976438141)
                    ·
                      refine ⟨77956119485046741164303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 207882985293457976438141 77956119485046741164303)
                      ·
                        rfl

theorem cell23_151819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 3, 3].length) (baseStart_151819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151819 prefixEnd_151819 := by exact prefixLift 151819
  have htrace : WordTrace (prefixWord ++ tailWord_151819) baseStart_151819 baseEnd_151819 := by
    simpa [prefixWord, tailWord_151819, baseEnd_151819] using wordTrace_append hprefix tailTrace_151819
  have hstable : (prefixWord ++ tailWord_151819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151819).length < 2 ^ (prefixWord ++ tailWord_151819).sum := by decide
  have hdescent : baseEnd_151819 < baseStart_151819 := by decide
  rcases family_descends (prefixWord ++ tailWord_151819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151839 : List Nat := [1, 1, 2, 4, 3, 2, 1, 1, 1, 7]
def baseStart_151839 : Nat := 118140960795 + 151839 * 2 ^ 59
def prefixEnd_151839 : Nat := 4983230072969 + 3 ^ 40 * 151839 * 2
def baseEnd_151839 : Nat := 25988796366045554304737

theorem tailTrace_151839 : CollatzResearch.WordTrace tailWord_151839 prefixEnd_151839 25988796366045554304737 := by
  unfold tailWord_151839
  simp only [CollatzResearch.WordTrace]
  refine ⟨5538023296920709881754571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3692015531280473254503047 5538023296920709881754571)
  ·
    refine ⟨8307034945381064822631857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5538023296920709881754571 8307034945381064822631857)
    ·
      refine ⟨6230276209035798616973893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8307034945381064822631857 6230276209035798616973893)
      ·
        refine ⟨1168176789194212240682605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6230276209035798616973893 1168176789194212240682605)
        ·
          refine ⟨438066295947829590255977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1168176789194212240682605 438066295947829590255977)
          ·
            refine ⟨328549721960872192691983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 438066295947829590255977 328549721960872192691983)
            ·
              refine ⟨492824582941308289037975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 328549721960872192691983 492824582941308289037975)
              ·
                refine ⟨739236874411962433556963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 492824582941308289037975 739236874411962433556963)
                ·
                  refine ⟨1108855311617943650335445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 739236874411962433556963 1108855311617943650335445)
                  ·
                    refine ⟨25988796366045554304737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1108855311617943650335445 25988796366045554304737)
                    ·
                      rfl

theorem cell23_151839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 7].length) (baseStart_151839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151839 prefixEnd_151839 := by exact prefixLift 151839
  have htrace : WordTrace (prefixWord ++ tailWord_151839) baseStart_151839 baseEnd_151839 := by
    simpa [prefixWord, tailWord_151839, baseEnd_151839] using wordTrace_append hprefix tailTrace_151839
  have hstable : (prefixWord ++ tailWord_151839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151839).length < 2 ^ (prefixWord ++ tailWord_151839).sum := by decide
  have hdescent : baseEnd_151839 < baseStart_151839 := by decide
  rcases family_descends (prefixWord ++ tailWord_151839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151854 : List Nat := [4, 1, 3, 3, 1, 2, 1, 2, 2, 2, 2]
def baseStart_151854 : Nat := 118140960795 + 151854 * 2 ^ 59
def prefixEnd_151854 : Nat := 4983230072969 + 3 ^ 40 * 151854 * 2
def baseEnd_151854 : Nat := 77974091307954104226643

theorem tailTrace_151854 : CollatzResearch.WordTrace tailWord_151854 prefixEnd_151854 77974091307954104226643 := by
  unfold tailWord_151854
  simp only [CollatzResearch.WordTrace]
  refine ⟨692321298983295930443827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3692380261244244962367077 692321298983295930443827)
  ·
    refine ⟨1038481948474943895665741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 692321298983295930443827 1038481948474943895665741)
    ·
      refine ⟨389430730678103960874653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1038481948474943895665741 389430730678103960874653)
      ·
        refine ⟨146036524004288985327995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 389430730678103960874653 146036524004288985327995)
        ·
          refine ⟨219054786006433477991993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146036524004288985327995 219054786006433477991993)
          ·
            refine ⟨164291089504825108493995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219054786006433477991993 164291089504825108493995)
            ·
              refine ⟨246436634257237662740993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164291089504825108493995 246436634257237662740993)
              ·
                refine ⟨184827475692928247055745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 246436634257237662740993 184827475692928247055745)
                ·
                  refine ⟨138620606769696185291809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 184827475692928247055745 138620606769696185291809)
                  ·
                    refine ⟨103965455077272138968857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 138620606769696185291809 103965455077272138968857)
                    ·
                      refine ⟨77974091307954104226643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 103965455077272138968857 77974091307954104226643)
                      ·
                        rfl

theorem cell23_151854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_151854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151854 prefixEnd_151854 := by exact prefixLift 151854
  have htrace : WordTrace (prefixWord ++ tailWord_151854) baseStart_151854 baseEnd_151854 := by
    simpa [prefixWord, tailWord_151854, baseEnd_151854] using wordTrace_append hprefix tailTrace_151854
  have hstable : (prefixWord ++ tailWord_151854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151854).length < 2 ^ (prefixWord ++ tailWord_151854).sum := by decide
  have hdescent : baseEnd_151854 < baseStart_151854 := by decide
  rcases family_descends (prefixWord ++ tailWord_151854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151859 : List Nat := [1, 1, 1, 2, 5, 1, 2, 1, 4, 1, 4]
def baseStart_151859 : Nat := 118140960795 + 151859 * 2 ^ 59
def prefixEnd_151859 : Nat := 4983230072969 + 3 ^ 40 * 151859 * 2
def baseEnd_151859 : Nat := 77976658711226584664119

theorem tailTrace_151859 : CollatzResearch.WordTrace tailWord_151859 prefixEnd_151859 77976658711226584664119 := by
  unfold tailWord_151859
  simp only [CollatzResearch.WordTrace]
  refine ⟨5538752756848253297482631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3692501837898835531655087 5538752756848253297482631)
  ·
    refine ⟨8308129135272379946223947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5538752756848253297482631 8308129135272379946223947)
    ·
      refine ⟨12462193702908569919335921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8308129135272379946223947 12462193702908569919335921)
      ·
        refine ⟨9346645277181427439501941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12462193702908569919335921 9346645277181427439501941)
        ·
          refine ⟨876247994735758822453307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9346645277181427439501941 876247994735758822453307)
          ·
            refine ⟨1314371992103638233679961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 876247994735758822453307 1314371992103638233679961)
            ·
              refine ⟨985778994077728675259971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1314371992103638233679961 985778994077728675259971)
              ·
                refine ⟨1478668491116593012889957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 985778994077728675259971 1478668491116593012889957)
                ·
                  refine ⟨277250342084361189916867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1478668491116593012889957 277250342084361189916867)
                  ·
                    refine ⟨415875513126541784875301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 277250342084361189916867 415875513126541784875301)
                    ·
                      refine ⟨77976658711226584664119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 415875513126541784875301 77976658711226584664119)
                      ·
                        rfl

theorem cell23_151859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 4, 1, 4].length) (baseStart_151859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151859 prefixEnd_151859 := by exact prefixLift 151859
  have htrace : WordTrace (prefixWord ++ tailWord_151859) baseStart_151859 baseEnd_151859 := by
    simpa [prefixWord, tailWord_151859, baseEnd_151859] using wordTrace_append hprefix tailTrace_151859
  have hstable : (prefixWord ++ tailWord_151859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151859).length < 2 ^ (prefixWord ++ tailWord_151859).sum := by decide
  have hdescent : baseEnd_151859 < baseStart_151859 := by decide
  rcases family_descends (prefixWord ++ tailWord_151859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151879 : List Nat := [1, 1, 4, 1, 2, 2, 1, 1, 3, 4, 3]
def baseStart_151879 : Nat := 118140960795 + 151879 * 2 ^ 59
def prefixEnd_151879 : Nat := 4983230072969 + 3 ^ 40 * 151879 * 2
def baseEnd_151879 : Nat := 77986928324316506414027

theorem tailTrace_151879 : CollatzResearch.WordTrace tailWord_151879 prefixEnd_151879 77986928324316506414027 := by
  unfold tailWord_151879
  simp only [CollatzResearch.WordTrace]
  refine ⟨5539482216775796713210691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3692988144517197808807127 5539482216775796713210691)
  ·
    refine ⟨8309223325163695069816037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5539482216775796713210691 8309223325163695069816037)
    ·
      refine ⟨1557979373468192825590507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8309223325163695069816037 1557979373468192825590507)
      ·
        refine ⟨2336969060202289238385761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1557979373468192825590507 2336969060202289238385761)
        ·
          refine ⟨1752726795151716928789321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2336969060202289238385761 1752726795151716928789321)
          ·
            refine ⟨1314545096363787696591991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1752726795151716928789321 1314545096363787696591991)
            ·
              refine ⟨1971817644545681544887987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1314545096363787696591991 1971817644545681544887987)
              ·
                refine ⟨2957726466818522317331981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1971817644545681544887987 2957726466818522317331981)
                ·
                  refine ⟨1109147425056945868999493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2957726466818522317331981 1109147425056945868999493)
                  ·
                    refine ⟨207965142198177350437405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1109147425056945868999493 207965142198177350437405)
                    ·
                      refine ⟨77986928324316506414027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 207965142198177350437405 77986928324316506414027)
                      ·
                        rfl

theorem cell23_151879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 4, 3].length) (baseStart_151879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151879 prefixEnd_151879 := by exact prefixLift 151879
  have htrace : WordTrace (prefixWord ++ tailWord_151879) baseStart_151879 baseEnd_151879 := by
    simpa [prefixWord, tailWord_151879, baseEnd_151879] using wordTrace_append hprefix tailTrace_151879
  have hstable : (prefixWord ++ tailWord_151879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151879).length < 2 ^ (prefixWord ++ tailWord_151879).sum := by decide
  have hdescent : baseEnd_151879 < baseStart_151879 := by decide
  rcases family_descends (prefixWord ++ tailWord_151879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151903 : List Nat := [1, 1, 2, 3, 1, 2, 5, 3, 1, 4]
def baseStart_151903 : Nat := 118140960795 + 151903 * 2 ^ 59
def prefixEnd_151903 : Nat := 4983230072969 + 3 ^ 40 * 151903 * 2
def baseEnd_151903 : Nat := 25999750620008137504639

theorem tailTrace_151903 : CollatzResearch.WordTrace tailWord_151903 prefixEnd_151903 25999750620008137504639 := by
  unfold tailWord_151903
  simp only [CollatzResearch.WordTrace]
  refine ⟨5540357568688848812084363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3693571712459232541389575 5540357568688848812084363)
  ·
    refine ⟨8310536353033273218126545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5540357568688848812084363 8310536353033273218126545)
    ·
      refine ⟨6232902264774954913594909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8310536353033273218126545 6232902264774954913594909)
      ·
        refine ⟨2337338349290608092598091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6232902264774954913594909 2337338349290608092598091)
        ·
          refine ⟨3506007523935912138897137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2337338349290608092598091 3506007523935912138897137)
          ·
            refine ⟨2629505642951934104172853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3506007523935912138897137 2629505642951934104172853)
            ·
              refine ⟨246516154026743822266205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2629505642951934104172853 246516154026743822266205)
              ·
                refine ⟨92443557760028933349827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 246516154026743822266205 92443557760028933349827)
                ·
                  refine ⟨138665336640043400024741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92443557760028933349827 138665336640043400024741)
                  ·
                    refine ⟨25999750620008137504639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 138665336640043400024741 25999750620008137504639)
                    ·
                      rfl

theorem cell23_151903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 3, 1, 4].length) (baseStart_151903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151903 prefixEnd_151903 := by exact prefixLift 151903
  have htrace : WordTrace (prefixWord ++ tailWord_151903) baseStart_151903 baseEnd_151903 := by
    simpa [prefixWord, tailWord_151903, baseEnd_151903] using wordTrace_append hprefix tailTrace_151903
  have hstable : (prefixWord ++ tailWord_151903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151903).length < 2 ^ (prefixWord ++ tailWord_151903).sum := by decide
  have hdescent : baseEnd_151903 < baseStart_151903 := by decide
  rcases family_descends (prefixWord ++ tailWord_151903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151920 : List Nat := [2, 1, 1, 1, 4, 4, 3, 2, 1, 4]
def baseStart_151920 : Nat := 118140960795 + 151920 * 2 ^ 59
def prefixEnd_151920 : Nat := 4983230072969 + 3 ^ 40 * 151920 * 2
def baseEnd_151920 : Nat := 26002660343716948667113

theorem tailTrace_151920 : CollatzResearch.WordTrace tailWord_151920 prefixEnd_151920 26002660343716948667113 := by
  unfold tailWord_151920
  simp only [CollatzResearch.WordTrace]
  refine ⟨2770488804813630357726607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3693985073084840476968809 2770488804813630357726607)
  ·
    refine ⟨4155733207220445536589911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2770488804813630357726607 4155733207220445536589911)
    ·
      refine ⟨6233599810830668304884867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4155733207220445536589911 6233599810830668304884867)
      ·
        refine ⟨9350399716246002457327301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6233599810830668304884867 9350399716246002457327301)
        ·
          refine ⟨1753199946796125460748869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9350399716246002457327301 1753199946796125460748869)
          ·
            refine ⟨328724990024273523890413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1753199946796125460748869 328724990024273523890413)
            ·
              refine ⟨123271871259102571458905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 328724990024273523890413 123271871259102571458905)
              ·
                refine ⟨92453903444326928594179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123271871259102571458905 92453903444326928594179)
                ·
                  refine ⟨138680855166490392891269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92453903444326928594179 138680855166490392891269)
                  ·
                    refine ⟨26002660343716948667113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 138680855166490392891269 26002660343716948667113)
                    ·
                      rfl

theorem cell23_151920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 2, 1, 4].length) (baseStart_151920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151920 prefixEnd_151920 := by exact prefixLift 151920
  have htrace : WordTrace (prefixWord ++ tailWord_151920) baseStart_151920 baseEnd_151920 := by
    simpa [prefixWord, tailWord_151920, baseEnd_151920] using wordTrace_append hprefix tailTrace_151920
  have hstable : (prefixWord ++ tailWord_151920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151920).length < 2 ^ (prefixWord ++ tailWord_151920).sum := by decide
  have hdescent : baseEnd_151920 < baseStart_151920 := by decide
  rcases family_descends (prefixWord ++ tailWord_151920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151929 : List Nat := [1, 2, 1, 3, 2, 1, 1, 4, 3, 5]
def baseStart_151929 : Nat := 118140960795 + 151929 * 2 ^ 59
def prefixEnd_151929 : Nat := 4983230072969 + 3 ^ 40 * 151929 * 2
def baseEnd_151929 : Nat := 26004200785680436929599

theorem tailTrace_151929 : CollatzResearch.WordTrace tailWord_151929 prefixEnd_151929 26004200785680436929599 := by
  unfold tailWord_151929
  simp only [CollatzResearch.WordTrace]
  refine ⟨5541305866594655252530841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3694203911063103501687227 5541305866594655252530841)
  ·
    refine ⟨4155979399945991439398131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5541305866594655252530841 4155979399945991439398131)
    ·
      refine ⟨6233969099918987159097197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4155979399945991439398131 6233969099918987159097197)
      ·
        refine ⟨2337738412469620184661449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6233969099918987159097197 2337738412469620184661449)
        ·
          refine ⟨1753303809352215138496087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2337738412469620184661449 1753303809352215138496087)
          ·
            refine ⟨2629955714028322707744131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1753303809352215138496087 2629955714028322707744131)
            ·
              refine ⟨3944933571042484061616197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2629955714028322707744131 3944933571042484061616197)
              ·
                refine ⟨739675044570465761553037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3944933571042484061616197 739675044570465761553037)
                ·
                  refine ⟨277378141713924660582389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 739675044570465761553037 277378141713924660582389)
                  ·
                    refine ⟨26004200785680436929599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 277378141713924660582389 26004200785680436929599)
                    ·
                      rfl

theorem cell23_151929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 3, 5].length) (baseStart_151929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151929 prefixEnd_151929 := by exact prefixLift 151929
  have htrace : WordTrace (prefixWord ++ tailWord_151929) baseStart_151929 baseEnd_151929 := by
    simpa [prefixWord, tailWord_151929, baseEnd_151929] using wordTrace_append hprefix tailTrace_151929
  have hstable : (prefixWord ++ tailWord_151929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151929).length < 2 ^ (prefixWord ++ tailWord_151929).sum := by decide
  have hdescent : baseEnd_151929 < baseStart_151929 := by decide
  rcases family_descends (prefixWord ++ tailWord_151929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151933 : List Nat := [1, 4, 1, 1, 2, 5, 2, 1, 6]
def baseStart_151933 : Nat := 118140960795 + 151933 * 2 ^ 59
def prefixEnd_151933 : Nat := 4983230072969 + 3 ^ 40 * 151933 * 2
def baseEnd_151933 : Nat := 8668295142184366126531

theorem tailTrace_151933 : CollatzResearch.WordTrace tailWord_151933 prefixEnd_151933 8668295142184366126531 := by
  unfold tailWord_151933
  simp only [CollatzResearch.WordTrace]
  refine ⟨5541451758580163935676453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3694301172386775957117635 5541451758580163935676453)
  ·
    refine ⟨1039022204733780737939335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5541451758580163935676453 1039022204733780737939335)
    ·
      refine ⟨1558533307100671106909003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1039022204733780737939335 1558533307100671106909003)
      ·
        refine ⟨2337799960651006660363505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1558533307100671106909003 2337799960651006660363505)
        ·
          refine ⟨1753349970488254995272629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2337799960651006660363505 1753349970488254995272629)
          ·
            refine ⟨164376559733273905806809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1753349970488254995272629 164376559733273905806809)
            ·
              refine ⟨123282419799955429355107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164376559733273905806809 123282419799955429355107)
              ·
                refine ⟨184923629699933144032661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123282419799955429355107 184923629699933144032661)
                ·
                  refine ⟨8668295142184366126531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 184923629699933144032661 8668295142184366126531)
                  ·
                    rfl

theorem cell23_151933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 1, 6].length) (baseStart_151933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151933 prefixEnd_151933 := by exact prefixLift 151933
  have htrace : WordTrace (prefixWord ++ tailWord_151933) baseStart_151933 baseEnd_151933 := by
    simpa [prefixWord, tailWord_151933, baseEnd_151933] using wordTrace_append hprefix tailTrace_151933
  have hstable : (prefixWord ++ tailWord_151933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151933).length < 2 ^ (prefixWord ++ tailWord_151933).sum := by decide
  have hdescent : baseEnd_151933 < baseStart_151933 := by decide
  rcases family_descends (prefixWord ++ tailWord_151933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151959 : List Nat := [1, 1, 3, 3, 1, 1, 3, 1, 3, 6]
def baseStart_151959 : Nat := 118140960795 + 151959 * 2 ^ 59
def prefixEnd_151959 : Nat := 4983230072969 + 3 ^ 40 * 151959 * 2
def baseEnd_151959 : Nat := 26009335592225397804553

theorem tailTrace_151959 : CollatzResearch.WordTrace tailWord_151959 prefixEnd_151959 26009335592225397804553 := by
  unfold tailWord_151959
  simp only [CollatzResearch.WordTrace]
  refine ⟨5542400056485970376122931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3694933370990646917415287 5542400056485970376122931)
  ·
    refine ⟨8313600084728955564184397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5542400056485970376122931 8313600084728955564184397)
    ·
      refine ⟨3117600031773358336569149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8313600084728955564184397 3117600031773358336569149)
      ·
        refine ⟨1169100011915009376213431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3117600031773358336569149 1169100011915009376213431)
        ·
          refine ⟨1753650017872514064320147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1169100011915009376213431 1753650017872514064320147)
          ·
            refine ⟨2630475026808771096480221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1753650017872514064320147 2630475026808771096480221)
            ·
              refine ⟨986428135053289161180083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2630475026808771096480221 986428135053289161180083)
              ·
                refine ⟨1479642202579933741770125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 986428135053289161180083 1479642202579933741770125)
                ·
                  refine ⟨554865825967475153163797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1479642202579933741770125 554865825967475153163797)
                  ·
                    refine ⟨26009335592225397804553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 554865825967475153163797 26009335592225397804553)
                    ·
                      rfl

theorem cell23_151959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 6].length) (baseStart_151959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151959 prefixEnd_151959 := by exact prefixLift 151959
  have htrace : WordTrace (prefixWord ++ tailWord_151959) baseStart_151959 baseEnd_151959 := by
    simpa [prefixWord, tailWord_151959, baseEnd_151959] using wordTrace_append hprefix tailTrace_151959
  have hstable : (prefixWord ++ tailWord_151959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151959).length < 2 ^ (prefixWord ++ tailWord_151959).sum := by decide
  have hdescent : baseEnd_151959 < baseStart_151959 := by decide
  rcases family_descends (prefixWord ++ tailWord_151959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151986 : List Nat := [3, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3]
def baseStart_151986 : Nat := 118140960795 + 151986 * 2 ^ 59
def prefixEnd_151986 : Nat := 4983230072969 + 3 ^ 40 * 151986 * 2
def baseEnd_151986 : Nat := 78041870754347587776035

theorem tailTrace_151986 : CollatzResearch.WordTrace tailWord_151986 prefixEnd_151986 78041870754347587776035 := by
  unfold tailWord_151986
  simp only [CollatzResearch.WordTrace]
  refine ⟨1385846206847038496838953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3695589884925435991570541 1385846206847038496838953)
  ·
    refine ⟨1039384655135278872629215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1385846206847038496838953 1039384655135278872629215)
    ·
      refine ⟨1559076982702918308943823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1039384655135278872629215 1559076982702918308943823)
      ·
        refine ⟨2338615474054377463415735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1559076982702918308943823 2338615474054377463415735)
        ·
          refine ⟨3507923211081566195123603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2338615474054377463415735 3507923211081566195123603)
          ·
            refine ⟨5261884816622349292685405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3507923211081566195123603 5261884816622349292685405)
            ·
              refine ⟨1973206806233380984757027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5261884816622349292685405 1973206806233380984757027)
              ·
                refine ⟨2959810209350071477135541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1973206806233380984757027 2959810209350071477135541)
                ·
                  refine ⟨277482207126569200981457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2959810209350071477135541 277482207126569200981457)
                  ·
                    refine ⟨208111655344926900736093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 277482207126569200981457 208111655344926900736093)
                    ·
                      refine ⟨78041870754347587776035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 208111655344926900736093 78041870754347587776035)
                      ·
                        rfl

theorem cell23_151986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3].length) (baseStart_151986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151986 prefixEnd_151986 := by exact prefixLift 151986
  have htrace : WordTrace (prefixWord ++ tailWord_151986) baseStart_151986 baseEnd_151986 := by
    simpa [prefixWord, tailWord_151986, baseEnd_151986] using wordTrace_append hprefix tailTrace_151986
  have hstable : (prefixWord ++ tailWord_151986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151986).length < 2 ^ (prefixWord ++ tailWord_151986).sum := by decide
  have hdescent : baseEnd_151986 < baseStart_151986 := by decide
  rcases family_descends (prefixWord ++ tailWord_151986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151993 : List Nat := [1, 2, 1, 4, 3, 1, 2, 3, 2, 4]
def baseStart_151993 : Nat := 118140960795 + 151993 * 2 ^ 59
def prefixEnd_151993 : Nat := 4983230072969 + 3 ^ 40 * 151993 * 2
def baseEnd_151993 : Nat := 26015155039643020129501

theorem tailTrace_151993 : CollatzResearch.WordTrace tailWord_151993 prefixEnd_151993 26015155039643020129501 := by
  unfold tailWord_151993
  simp only [CollatzResearch.WordTrace]
  refine ⟨5543640138362794182860633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3695760092241862788573755 5543640138362794182860633)
  ·
    refine ⟨4157730103772095637145475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5543640138362794182860633 4157730103772095637145475)
    ·
      refine ⟨6236595155658143455718213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4157730103772095637145475 6236595155658143455718213)
      ·
        refine ⟨1169361591685901897947165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6236595155658143455718213 1169361591685901897947165)
        ·
          refine ⟨438510596882213211730187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1169361591685901897947165 438510596882213211730187)
          ·
            refine ⟨657765895323319817595281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 438510596882213211730187 657765895323319817595281)
            ·
              refine ⟨493324421492489863196461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 657765895323319817595281 493324421492489863196461)
              ·
                refine ⟨184996658059683698698673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 493324421492489863196461 184996658059683698698673)
                ·
                  refine ⟨138747493544762774024005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 184996658059683698698673 138747493544762774024005)
                  ·
                    refine ⟨26015155039643020129501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 138747493544762774024005 26015155039643020129501)
                    ·
                      rfl

theorem cell23_151993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 3, 2, 4].length) (baseStart_151993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_151993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_151993 prefixEnd_151993 := by exact prefixLift 151993
  have htrace : WordTrace (prefixWord ++ tailWord_151993) baseStart_151993 baseEnd_151993 := by
    simpa [prefixWord, tailWord_151993, baseEnd_151993] using wordTrace_append hprefix tailTrace_151993
  have hstable : (prefixWord ++ tailWord_151993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151993).length < 2 ^ (prefixWord ++ tailWord_151993).sum := by decide
  have hdescent : baseEnd_151993 < baseStart_151993 := by decide
  rcases family_descends (prefixWord ++ tailWord_151993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152004 : List Nat := [2, 3, 3, 2, 3, 1, 1, 1, 2, 3, 2]
def baseStart_152004 : Nat := 118140960795 + 152004 * 2 ^ 59
def prefixEnd_152004 : Nat := 4983230072969 + 3 ^ 40 * 152004 * 2
def baseEnd_152004 : Nat := 78051113406128517350953

theorem tailTrace_152004 : CollatzResearch.WordTrace tailWord_152004 prefixEnd_152004 78051113406128517350953 := by
  unfold tailWord_152004
  simp only [CollatzResearch.WordTrace]
  refine ⟨2772020670661471530755533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3696027560881962041007377 2772020670661471530755533)
  ·
    refine ⟨1039507751498051824033325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2772020670661471530755533 1039507751498051824033325)
    ·
      refine ⟨389815406811769434012497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1039507751498051824033325 389815406811769434012497)
      ·
        refine ⟨292361555108827075509373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 389815406811769434012497 292361555108827075509373)
        ·
          refine ⟨109635583165810153316015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 292361555108827075509373 109635583165810153316015)
          ·
            refine ⟨164453374748715229974023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109635583165810153316015 164453374748715229974023)
            ·
              refine ⟨246680062123072844961035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164453374748715229974023 246680062123072844961035)
              ·
                refine ⟨370020093184609267441553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 246680062123072844961035 370020093184609267441553)
                ·
                  refine ⟨277515069888456950581165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 370020093184609267441553 277515069888456950581165)
                  ·
                    refine ⟨104068151208171356467937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 277515069888456950581165 104068151208171356467937)
                    ·
                      refine ⟨78051113406128517350953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 104068151208171356467937 78051113406128517350953)
                      ·
                        rfl

theorem cell23_152004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_152004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_152004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_152004 prefixEnd_152004 := by exact prefixLift 152004
  have htrace : WordTrace (prefixWord ++ tailWord_152004) baseStart_152004 baseEnd_152004 := by
    simpa [prefixWord, tailWord_152004, baseEnd_152004] using wordTrace_append hprefix tailTrace_152004
  have hstable : (prefixWord ++ tailWord_152004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152004).length < 2 ^ (prefixWord ++ tailWord_152004).sum := by decide
  have hdescent : baseEnd_152004 < baseStart_152004 := by decide
  rcases family_descends (prefixWord ++ tailWord_152004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152020 : List Nat := [2, 4, 1, 2, 2, 2, 1, 3, 1, 2, 3]
def baseStart_152020 : Nat := 118140960795 + 152020 * 2 ^ 59
def prefixEnd_152020 : Nat := 4983230072969 + 3 ^ 40 * 152020 * 2
def baseEnd_152020 : Nat := 78059329096600454750879

theorem tailTrace_152020 : CollatzResearch.WordTrace tailWord_152020 prefixEnd_152020 78059329096600454750879 := by
  unfold tailWord_152020
  simp only [CollatzResearch.WordTrace]
  refine ⟨2772312454632488897046757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3696416606176651862729009 2772312454632488897046757)
  ·
    refine ⟨519808585243591668196267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2772312454632488897046757 519808585243591668196267)
    ·
      refine ⟨779712877865387502294401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 519808585243591668196267 779712877865387502294401)
      ·
        refine ⟨584784658399040626720801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 779712877865387502294401 584784658399040626720801)
        ·
          refine ⟨438588493799280470040601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 584784658399040626720801 438588493799280470040601)
          ·
            refine ⟨328941370349460352530451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 438588493799280470040601 328941370349460352530451)
            ·
              refine ⟨493412055524190528795677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 328941370349460352530451 493412055524190528795677)
              ·
                refine ⟨185029520821571448298379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 493412055524190528795677 185029520821571448298379)
                ·
                  refine ⟨277544281232357172447569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 185029520821571448298379 277544281232357172447569)
                  ·
                    refine ⟨208158210924267879335677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 277544281232357172447569 208158210924267879335677)
                    ·
                      refine ⟨78059329096600454750879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 208158210924267879335677 78059329096600454750879)
                      ·
                        rfl

theorem cell23_152020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_152020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_152020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_152020 prefixEnd_152020 := by exact prefixLift 152020
  have htrace : WordTrace (prefixWord ++ tailWord_152020) baseStart_152020 baseEnd_152020 := by
    simpa [prefixWord, tailWord_152020, baseEnd_152020] using wordTrace_append hprefix tailTrace_152020
  have hstable : (prefixWord ++ tailWord_152020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152020).length < 2 ^ (prefixWord ++ tailWord_152020).sum := by decide
  have hdescent : baseEnd_152020 < baseStart_152020 := by decide
  rcases family_descends (prefixWord ++ tailWord_152020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152033 : List Nat := [1, 2, 3, 1, 2, 2, 3, 1, 4, 1, 3]
def baseStart_152033 : Nat := 118140960795 + 152033 * 2 ^ 59
def prefixEnd_152033 : Nat := 4983230072969 + 3 ^ 40 * 152033 * 2
def baseEnd_152033 : Nat := 78066004345108903888319

theorem tailTrace_152033 : CollatzResearch.WordTrace tailWord_152033 prefixEnd_152033 78066004345108903888319 := by
  unfold tailWord_152033
  simp only [CollatzResearch.WordTrace]
  refine ⟨5545099058217881014316753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3696732705478587342877835 5545099058217881014316753)
  ·
    refine ⟨4158824293663410760737565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5545099058217881014316753 4158824293663410760737565)
    ·
      refine ⟨1559559110123779035276587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4158824293663410760737565 1559559110123779035276587)
      ·
        refine ⟨2339338665185668552914881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1559559110123779035276587 2339338665185668552914881)
        ·
          refine ⟨1754503998889251414686161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2339338665185668552914881 1754503998889251414686161)
          ·
            refine ⟨1315877999166938561014621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1754503998889251414686161 1315877999166938561014621)
            ·
              refine ⟨493454249687601960380483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1315877999166938561014621 493454249687601960380483)
              ·
                refine ⟨740181374531402940570725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 493454249687601960380483 740181374531402940570725)
                ·
                  refine ⟨138784007724638051357011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 740181374531402940570725 138784007724638051357011)
                  ·
                    refine ⟨208176011586957077035517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 138784007724638051357011 208176011586957077035517)
                    ·
                      refine ⟨78066004345108903888319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 208176011586957077035517 78066004345108903888319)
                      ·
                        rfl

theorem cell23_152033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 4, 1, 3].length) (baseStart_152033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_152033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_152033 prefixEnd_152033 := by exact prefixLift 152033
  have htrace : WordTrace (prefixWord ++ tailWord_152033) baseStart_152033 baseEnd_152033 := by
    simpa [prefixWord, tailWord_152033, baseEnd_152033] using wordTrace_append hprefix tailTrace_152033
  have hstable : (prefixWord ++ tailWord_152033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152033).length < 2 ^ (prefixWord ++ tailWord_152033).sum := by decide
  have hdescent : baseEnd_152033 < baseStart_152033 := by decide
  rcases family_descends (prefixWord ++ tailWord_152033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152076 : List Nat := [2, 2, 1, 2, 4, 1, 1, 1, 1, 3, 5]
def baseStart_152076 : Nat := 118140960795 + 152076 * 2 ^ 59
def prefixEnd_152076 : Nat := 4983230072969 + 3 ^ 40 * 152076 * 2
def baseEnd_152076 : Nat := 78088084013252235650621

theorem tailTrace_152076 : CollatzResearch.WordTrace tailWord_152076 prefixEnd_152076 78088084013252235650621 := by
  unfold tailWord_152076
  simp only [CollatzResearch.WordTrace]
  refine ⟨2773333698531049679066041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3697778264708066238754721 2773333698531049679066041)
  ·
    refine ⟨2080000273898287259299531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2773333698531049679066041 2080000273898287259299531)
    ·
      refine ⟨3120000410847430888949297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2080000273898287259299531 3120000410847430888949297)
      ·
        refine ⟨2340000308135573166711973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3120000410847430888949297 2340000308135573166711973)
        ·
          refine ⟨438750057775419968758495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2340000308135573166711973 438750057775419968758495)
          ·
            refine ⟨658125086663129953137743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 438750057775419968758495 658125086663129953137743)
            ·
              refine ⟨987187629994694929706615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 658125086663129953137743 987187629994694929706615)
              ·
                refine ⟨1480781444992042394559923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 987187629994694929706615 1480781444992042394559923)
                ·
                  refine ⟨2221172167488063591839885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1480781444992042394559923 2221172167488063591839885)
                  ·
                    refine ⟨832939562808023846939957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2221172167488063591839885 832939562808023846939957)
                    ·
                      refine ⟨78088084013252235650621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 832939562808023846939957 78088084013252235650621)
                      ·
                        rfl

theorem cell23_152076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_152076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_152076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_152076 prefixEnd_152076 := by exact prefixLift 152076
  have htrace : WordTrace (prefixWord ++ tailWord_152076) baseStart_152076 baseEnd_152076 := by
    simpa [prefixWord, tailWord_152076, baseEnd_152076] using wordTrace_append hprefix tailTrace_152076
  have hstable : (prefixWord ++ tailWord_152076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152076).length < 2 ^ (prefixWord ++ tailWord_152076).sum := by decide
  have hdescent : baseEnd_152076 < baseStart_152076 := by decide
  rcases family_descends (prefixWord ++ tailWord_152076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152079 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 11]
def baseStart_152079 : Nat := 118140960795 + 152079 * 2 ^ 59
def prefixEnd_152079 : Nat := 4983230072969 + 3 ^ 40 * 152079 * 2
def baseEnd_152079 : Nat := 8676624939468413768123

theorem tailTrace_152079 : CollatzResearch.WordTrace tailWord_152079 prefixEnd_152079 8676624939468413768123 := by
  unfold tailWord_152079
  simp only [CollatzResearch.WordTrace]
  refine ⟨5546776816051230870491291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3697851210700820580327527 5546776816051230870491291)
  ·
    refine ⟨8320165224076846305736937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5546776816051230870491291 8320165224076846305736937)
    ·
      refine ⟨6240123918057634729302703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8320165224076846305736937 6240123918057634729302703)
      ·
        refine ⟨9360185877086452093954055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6240123918057634729302703 9360185877086452093954055)
        ·
          refine ⟨14040278815629678140931083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9360185877086452093954055 14040278815629678140931083)
          ·
            refine ⟨21060418223444517211396625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14040278815629678140931083 21060418223444517211396625)
            ·
              refine ⟨15795313667583387908547469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21060418223444517211396625 15795313667583387908547469)
              ·
                refine ⟨5923242625343770465705301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15795313667583387908547469 5923242625343770465705301)
                ·
                  refine ⟨8676624939468413768123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 5923242625343770465705301 8676624939468413768123)
                  ·
                    rfl

theorem cell23_152079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 11].length) (baseStart_152079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_152079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_152079 prefixEnd_152079 := by exact prefixLift 152079
  have htrace : WordTrace (prefixWord ++ tailWord_152079) baseStart_152079 baseEnd_152079 := by
    simpa [prefixWord, tailWord_152079, baseEnd_152079] using wordTrace_append hprefix tailTrace_152079
  have hstable : (prefixWord ++ tailWord_152079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152079).length < 2 ^ (prefixWord ++ tailWord_152079).sum := by decide
  have hdescent : baseEnd_152079 < baseStart_152079 := by decide
  rcases family_descends (prefixWord ++ tailWord_152079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152090 : List Nat := [3, 1, 1, 3, 1, 1, 4, 1, 4, 2, 2]
def baseStart_152090 : Nat := 118140960795 + 152090 * 2 ^ 59
def prefixEnd_152090 : Nat := 4983230072969 + 3 ^ 40 * 152090 * 2
def baseEnd_152090 : Nat := 78095272742415180875557

theorem tailTrace_152090 : CollatzResearch.WordTrace tailWord_152090 prefixEnd_152090 78095272742415180875557 := by
  unfold tailWord_152090
  simp only [CollatzResearch.WordTrace]
  refine ⟨1386794504752844937285431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3698118679340919832761149 1386794504752844937285431)
  ·
    refine ⟨2080191757129267405928147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1386794504752844937285431 2080191757129267405928147)
    ·
      refine ⟨3120287635693901108892221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2080191757129267405928147 3120287635693901108892221)
      ·
        refine ⟨1170107863385212915834583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3120287635693901108892221 1170107863385212915834583)
        ·
          refine ⟨1755161795077819373751875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1170107863385212915834583 1755161795077819373751875)
          ·
            refine ⟨2632742692616729060627813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1755161795077819373751875 2632742692616729060627813)
            ·
              refine ⟨493639254865636698867715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2632742692616729060627813 493639254865636698867715)
              ·
                refine ⟨740458882298455048301573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 493639254865636698867715 740458882298455048301573)
                ·
                  refine ⟨138836040430960321556545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 740458882298455048301573 138836040430960321556545)
                  ·
                    refine ⟨104127030323220241167409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 138836040430960321556545 104127030323220241167409)
                    ·
                      refine ⟨78095272742415180875557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 104127030323220241167409 78095272742415180875557)
                      ·
                        rfl

theorem cell23_152090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 4, 2, 2].length) (baseStart_152090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_152090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_152090 prefixEnd_152090 := by exact prefixLift 152090
  have htrace : WordTrace (prefixWord ++ tailWord_152090) baseStart_152090 baseEnd_152090 := by
    simpa [prefixWord, tailWord_152090, baseEnd_152090] using wordTrace_append hprefix tailTrace_152090
  have hstable : (prefixWord ++ tailWord_152090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152090).length < 2 ^ (prefixWord ++ tailWord_152090).sum := by decide
  have hdescent : baseEnd_152090 < baseStart_152090 := by decide
  rcases family_descends (prefixWord ++ tailWord_152090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152233 : List Nat := [1, 2, 1, 1, 1, 1, 2, 8, 1, 5]
def baseStart_152233 : Nat := 118140960795 + 152233 * 2 ^ 59
def prefixEnd_152233 : Nat := 4983230072969 + 3 ^ 40 * 152233 * 2
def baseEnd_152233 : Nat := 26056233492002707129133

theorem tailTrace_152233 : CollatzResearch.WordTrace tailWord_152233 prefixEnd_152233 26056233492002707129133 := by
  unfold tailWord_152233
  simp only [CollatzResearch.WordTrace]
  refine ⟨5552393657493315171597353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3701595771662210114398235 5552393657493315171597353)
  ·
    refine ⟨4164295243119986378698015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5552393657493315171597353 4164295243119986378698015)
    ·
      refine ⟨6246442864679979568047023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4164295243119986378698015 6246442864679979568047023)
      ·
        refine ⟨9369664297019969352070535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6246442864679979568047023 9369664297019969352070535)
        ·
          refine ⟨14054496445529954028105803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9369664297019969352070535 14054496445529954028105803)
          ·
            refine ⟨21081744668294931042158705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14054496445529954028105803 21081744668294931042158705)
            ·
              refine ⟨15811308501221198281619029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21081744668294931042158705 15811308501221198281619029)
              ·
                refine ⟨185288771498685917362723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 15811308501221198281619029 185288771498685917362723)
                ·
                  refine ⟨277933157248028876044085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 185288771498685917362723 277933157248028876044085)
                  ·
                    refine ⟨26056233492002707129133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 277933157248028876044085 26056233492002707129133)
                    ·
                      rfl

theorem cell23_152233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 8, 1, 5].length) (baseStart_152233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_152233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_152233 prefixEnd_152233 := by exact prefixLift 152233
  have htrace : WordTrace (prefixWord ++ tailWord_152233) baseStart_152233 baseEnd_152233 := by
    simpa [prefixWord, tailWord_152233, baseEnd_152233] using wordTrace_append hprefix tailTrace_152233
  have hstable : (prefixWord ++ tailWord_152233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152233).length < 2 ^ (prefixWord ++ tailWord_152233).sum := by decide
  have hdescent : baseEnd_152233 < baseStart_152233 := by decide
  rcases family_descends (prefixWord ++ tailWord_152233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152240 : List Nat := [2, 1, 1, 1, 2, 1, 3, 5, 2, 3, 2]
def baseStart_152240 : Nat := 118140960795 + 152240 * 2 ^ 59
def prefixEnd_152240 : Nat := 4983230072969 + 3 ^ 40 * 152240 * 2
def baseEnd_152240 : Nat := 78172294840589593999867

theorem tailTrace_152240 : CollatzResearch.WordTrace tailWord_152240 prefixEnd_152240 78172294840589593999867 := by
  unfold tailWord_152240
  simp only [CollatzResearch.WordTrace]
  refine ⟨2776324484233977683551087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3701765978978636911401449 2776324484233977683551087)
  ·
    refine ⟨4164486726350966525326631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2776324484233977683551087 4164486726350966525326631)
    ·
      refine ⟨6246730089526449787989947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4164486726350966525326631 6246730089526449787989947)
      ·
        refine ⟨9370095134289674681984921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6246730089526449787989947 9370095134289674681984921)
        ·
          refine ⟨7027571350717256011488691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9370095134289674681984921 7027571350717256011488691)
          ·
            refine ⟨10541357026075884017233037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7027571350717256011488691 10541357026075884017233037)
            ·
              refine ⟨3953008884778456506462389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10541357026075884017233037 3953008884778456506462389)
              ·
                refine ⟨370594582947980297480849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3953008884778456506462389 370594582947980297480849)
                ·
                  refine ⟨277945937210985223110637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 370594582947980297480849 277945937210985223110637)
                  ·
                    refine ⟨104229726454119458666489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 277945937210985223110637 104229726454119458666489)
                    ·
                      refine ⟨78172294840589593999867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 104229726454119458666489 78172294840589593999867)
                      ·
                        rfl

theorem cell23_152240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 2, 3, 2].length) (baseStart_152240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_152240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_152240 prefixEnd_152240 := by exact prefixLift 152240
  have htrace : WordTrace (prefixWord ++ tailWord_152240) baseStart_152240 baseEnd_152240 := by
    simpa [prefixWord, tailWord_152240, baseEnd_152240] using wordTrace_append hprefix tailTrace_152240
  have hstable : (prefixWord ++ tailWord_152240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152240).length < 2 ^ (prefixWord ++ tailWord_152240).sum := by decide
  have hdescent : baseEnd_152240 < baseStart_152240 := by decide
  rcases family_descends (prefixWord ++ tailWord_152240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152241 : List Nat := [1, 2, 2, 6, 1, 2, 1, 3, 1, 4]
def baseStart_152241 : Nat := 118140960795 + 152241 * 2 ^ 59
def prefixEnd_152241 : Nat := 4983230072969 + 3 ^ 40 * 152241 * 2
def baseEnd_152241 : Nat := 26057602773748030029121

theorem tailTrace_152241 : CollatzResearch.WordTrace tailWord_152241 prefixEnd_152241 26057602773748030029121 := by
  unfold tailWord_152241
  simp only [CollatzResearch.WordTrace]
  refine ⟨5552685441464332537888577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3701790294309555025259051 5552685441464332537888577)
  ·
    refine ⟨4164514081098249403416433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5552685441464332537888577 4164514081098249403416433)
    ·
      refine ⟨3123385560823687052562325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4164514081098249403416433 3123385560823687052562325)
      ·
        refine ⟨146408698163610330588859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3123385560823687052562325 146408698163610330588859)
        ·
          refine ⟨219613047245415495883289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146408698163610330588859 219613047245415495883289)
          ·
            refine ⟨164709785434061621912467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219613047245415495883289 164709785434061621912467)
            ·
              refine ⟨247064678151092432868701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164709785434061621912467 247064678151092432868701)
              ·
                refine ⟨92649254306659662325763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 247064678151092432868701 92649254306659662325763)
                ·
                  refine ⟨138973881459989493488645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92649254306659662325763 138973881459989493488645)
                  ·
                    refine ⟨26057602773748030029121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 138973881459989493488645 26057602773748030029121)
                    ·
                      rfl

theorem cell23_152241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 3, 1, 4].length) (baseStart_152241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_152241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_152241 prefixEnd_152241 := by exact prefixLift 152241
  have htrace : WordTrace (prefixWord ++ tailWord_152241) baseStart_152241 baseEnd_152241 := by
    simpa [prefixWord, tailWord_152241, baseEnd_152241] using wordTrace_append hprefix tailTrace_152241
  have hstable : (prefixWord ++ tailWord_152241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152241).length < 2 ^ (prefixWord ++ tailWord_152241).sum := by decide
  have hdescent : baseEnd_152241 < baseStart_152241 := by decide
  rcases family_descends (prefixWord ++ tailWord_152241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152273 : List Nat := [1, 2, 2, 1, 2, 3, 1, 4, 1, 1, 5]
def baseStart_152273 : Nat := 118140960795 + 152273 * 2 ^ 59
def prefixEnd_152273 : Nat := 4983230072969 + 3 ^ 40 * 152273 * 2
def baseEnd_152273 : Nat := 78189239702187964887215

theorem tailTrace_152273 : CollatzResearch.WordTrace tailWord_152273 prefixEnd_152273 78189239702187964887215 := by
  unfold tailWord_152273
  simp only [CollatzResearch.WordTrace]
  refine ⟨5553852577348402003053473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3702568384898934668702315 5553852577348402003053473)
  ·
    refine ⟨4165389433011301502290105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5553852577348402003053473 4165389433011301502290105)
    ·
      refine ⟨3124042074758476126717579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4165389433011301502290105 3124042074758476126717579)
      ·
        refine ⟨4686063112137714190076369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3124042074758476126717579 4686063112137714190076369)
        ·
          refine ⟨3514547334103285642557277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4686063112137714190076369 3514547334103285642557277)
          ·
            refine ⟨1317955250288732115958979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3514547334103285642557277 1317955250288732115958979)
            ·
              refine ⟨1976932875433098173938469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1317955250288732115958979 1976932875433098173938469)
              ·
                refine ⟨370674914143705907613463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1976932875433098173938469 370674914143705907613463)
                ·
                  refine ⟨556012371215558861420195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 370674914143705907613463 556012371215558861420195)
                  ·
                    refine ⟨834018556823338292130293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 556012371215558861420195 834018556823338292130293)
                    ·
                      refine ⟨78189239702187964887215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 834018556823338292130293 78189239702187964887215)
                      ·
                        rfl

theorem cell23_152273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 1, 5].length) (baseStart_152273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_152273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_152273 prefixEnd_152273 := by exact prefixLift 152273
  have htrace : WordTrace (prefixWord ++ tailWord_152273) baseStart_152273 baseEnd_152273 := by
    simpa [prefixWord, tailWord_152273, baseEnd_152273] using wordTrace_append hprefix tailTrace_152273
  have hstable : (prefixWord ++ tailWord_152273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152273).length < 2 ^ (prefixWord ++ tailWord_152273).sum := by decide
  have hdescent : baseEnd_152273 < baseStart_152273 := by decide
  rcases family_descends (prefixWord ++ tailWord_152273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152284 : List Nat := [2, 2, 5, 1, 1, 3, 1, 2, 1, 5]
def baseStart_152284 : Nat := 118140960795 + 152284 * 2 ^ 59
def prefixEnd_152284 : Nat := 4983230072969 + 3 ^ 40 * 152284 * 2
def baseEnd_152284 : Nat := 26064962663129140616555

theorem tailTrace_152284 : CollatzResearch.WordTrace tailWord_152284 prefixEnd_152284 26064962663129140616555 := by
  unfold tailWord_152284
  simp only [CollatzResearch.WordTrace]
  refine ⟨2777126890154275440851953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3702835853539033921135937 2777126890154275440851953)
  ·
    refine ⟨2082845167615706580638965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2777126890154275440851953 2082845167615706580638965)
    ·
      refine ⟨195266734463972491934903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2082845167615706580638965 195266734463972491934903)
      ·
        refine ⟨292900101695958737902355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195266734463972491934903 292900101695958737902355)
        ·
          refine ⟨439350152543938106853533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292900101695958737902355 439350152543938106853533)
          ·
            refine ⟨164756307203976790070075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 439350152543938106853533 164756307203976790070075)
            ·
              refine ⟨247134460805965185105113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164756307203976790070075 247134460805965185105113)
              ·
                refine ⟨185350845604473888828835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 247134460805965185105113 185350845604473888828835)
                ·
                  refine ⟨278026268406710833243253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 185350845604473888828835 278026268406710833243253)
                  ·
                    refine ⟨26064962663129140616555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 278026268406710833243253 26064962663129140616555)
                    ·
                      rfl

theorem cell23_152284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_152284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_152284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_152284 prefixEnd_152284 := by exact prefixLift 152284
  have htrace : WordTrace (prefixWord ++ tailWord_152284) baseStart_152284 baseEnd_152284 := by
    simpa [prefixWord, tailWord_152284, baseEnd_152284] using wordTrace_append hprefix tailTrace_152284
  have hstable : (prefixWord ++ tailWord_152284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152284).length < 2 ^ (prefixWord ++ tailWord_152284).sum := by decide
  have hdescent : baseEnd_152284 < baseStart_152284 := by decide
  rcases family_descends (prefixWord ++ tailWord_152284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152287 : List Nat := [1, 1, 2, 3, 2, 5, 1, 2, 1, 1, 4]
def baseStart_152287 : Nat := 118140960795 + 152287 * 2 ^ 59
def prefixEnd_152287 : Nat := 4983230072969 + 3 ^ 40 * 152287 * 2
def baseEnd_152287 : Nat := 78196428431350910112151

theorem tailTrace_152287 : CollatzResearch.WordTrace tailWord_152287 prefixEnd_152287 78196428431350910112151 := by
  unfold tailWord_152287
  simp only [CollatzResearch.WordTrace]
  refine ⟨5554363199297682394063115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3702908799531788262708743 5554363199297682394063115)
  ·
    refine ⟨8331544798946523591094673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5554363199297682394063115 8331544798946523591094673)
    ·
      refine ⟨6248658599209892693321005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8331544798946523591094673 6248658599209892693321005)
      ·
        refine ⟨2343246974703709759995377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6248658599209892693321005 2343246974703709759995377)
        ·
          refine ⟨1757435231027782319996533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2343246974703709759995377 1757435231027782319996533)
          ·
            refine ⟨164759552908854592499675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1757435231027782319996533 164759552908854592499675)
            ·
              refine ⟨247139329363281888749513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164759552908854592499675 247139329363281888749513)
              ·
                refine ⟨185354497022461416562135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 247139329363281888749513 185354497022461416562135)
                ·
                  refine ⟨278031745533692124843203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 185354497022461416562135 278031745533692124843203)
                  ·
                    refine ⟨417047618300538187264805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 278031745533692124843203 417047618300538187264805)
                    ·
                      refine ⟨78196428431350910112151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 417047618300538187264805 78196428431350910112151)
                      ·
                        rfl

theorem cell23_152287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 2, 1, 1, 4].length) (baseStart_152287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_152287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_152287 prefixEnd_152287 := by exact prefixLift 152287
  have htrace : WordTrace (prefixWord ++ tailWord_152287) baseStart_152287 baseEnd_152287 := by
    simpa [prefixWord, tailWord_152287, baseEnd_152287] using wordTrace_append hprefix tailTrace_152287
  have hstable : (prefixWord ++ tailWord_152287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152287).length < 2 ^ (prefixWord ++ tailWord_152287).sum := by decide
  have hdescent : baseEnd_152287 < baseStart_152287 := by decide
  rcases family_descends (prefixWord ++ tailWord_152287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152293 : List Nat := [1, 3, 1, 4, 1, 2, 2, 9]
def baseStart_152293 : Nat := 118140960795 + 152293 * 2 ^ 59
def prefixEnd_152293 : Nat := 4983230072969 + 3 ^ 40 * 152293 * 2
def baseEnd_152293 : Nat := 2896278122788069875449

theorem tailTrace_152293 : CollatzResearch.WordTrace tailWord_152293 prefixEnd_152293 2896278122788069875449 := by
  unfold tailWord_152293
  simp only [CollatzResearch.WordTrace]
  refine ⟨5554582037275945418781533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3703054691517296945854355 5554582037275945418781533)
  ·
    refine ⟨2082968263978479532043075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5554582037275945418781533 2082968263978479532043075)
    ·
      refine ⟨3124452395967719298064613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2082968263978479532043075 3124452395967719298064613)
      ·
        refine ⟨585834824243947368387115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3124452395967719298064613 585834824243947368387115)
        ·
          refine ⟨878752236365921052580673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 585834824243947368387115 878752236365921052580673)
          ·
            refine ⟨659064177274440789435505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 878752236365921052580673 659064177274440789435505)
            ·
              refine ⟨494298132955830592076629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 659064177274440789435505 494298132955830592076629)
              ·
                refine ⟨2896278122788069875449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 494298132955830592076629 2896278122788069875449)
                ·
                  rfl

theorem cell23_152293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 9].length) (baseStart_152293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_152293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_152293 prefixEnd_152293 := by exact prefixLift 152293
  have htrace : WordTrace (prefixWord ++ tailWord_152293) baseStart_152293 baseEnd_152293 := by
    simpa [prefixWord, tailWord_152293, baseEnd_152293] using wordTrace_append hprefix tailTrace_152293
  have hstable : (prefixWord ++ tailWord_152293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152293).length < 2 ^ (prefixWord ++ tailWord_152293).sum := by decide
  have hdescent : baseEnd_152293 < baseStart_152293 := by decide
  rcases family_descends (prefixWord ++ tailWord_152293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152304 : List Nat := [2, 1, 1, 1, 3, 1, 4, 5, 1, 2, 2]
def baseStart_152304 : Nat := 118140960795 + 152304 * 2 ^ 59
def prefixEnd_152304 : Nat := 4983230072969 + 3 ^ 40 * 152304 * 2
def baseEnd_152304 : Nat := 78205157602477343599573

theorem tailTrace_152304 : CollatzResearch.WordTrace tailWord_152304 prefixEnd_152304 78205157602477343599573 := by
  unfold tailWord_152304
  simp only [CollatzResearch.WordTrace]
  refine ⟨2777491620118047148715983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3703322160157396198287977 2777491620118047148715983)
  ·
    refine ⟨4166237430177070723073975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2777491620118047148715983 4166237430177070723073975)
    ·
      refine ⟨6249356145265606084610963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4166237430177070723073975 6249356145265606084610963)
      ·
        refine ⟨9374034217898409126916445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6249356145265606084610963 9374034217898409126916445)
        ·
          refine ⟨3515262831711903422593667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9374034217898409126916445 3515262831711903422593667)
          ·
            refine ⟨5272894247567855133890501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3515262831711903422593667 5272894247567855133890501)
            ·
              refine ⟨988667671418972837604469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5272894247567855133890501 988667671418972837604469)
              ·
                refine ⟨92687594195528703525419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 988667671418972837604469 92687594195528703525419)
                ·
                  refine ⟨139031391293293055288129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92687594195528703525419 139031391293293055288129)
                  ·
                    refine ⟨104273543469969791466097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 139031391293293055288129 104273543469969791466097)
                    ·
                      refine ⟨78205157602477343599573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 104273543469969791466097 78205157602477343599573)
                      ·
                        rfl

theorem cell23_152304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 5, 1, 2, 2].length) (baseStart_152304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_152304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_152304 prefixEnd_152304 := by exact prefixLift 152304
  have htrace : WordTrace (prefixWord ++ tailWord_152304) baseStart_152304 baseEnd_152304 := by
    simpa [prefixWord, tailWord_152304, baseEnd_152304] using wordTrace_append hprefix tailTrace_152304
  have hstable : (prefixWord ++ tailWord_152304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152304).length < 2 ^ (prefixWord ++ tailWord_152304).sum := by decide
  have hdescent : baseEnd_152304 < baseStart_152304 := by decide
  rcases family_descends (prefixWord ++ tailWord_152304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152337 : List Nat := [1, 2, 2, 1, 1, 3, 4, 3, 2, 1, 3]
def baseStart_152337 : Nat := 118140960795 + 152337 * 2 ^ 59
def prefixEnd_152337 : Nat := 4983230072969 + 3 ^ 40 * 152337 * 2
def baseEnd_152337 : Nat := 78222102464075714486921

theorem tailTrace_152337 : CollatzResearch.WordTrace tailWord_152337 prefixEnd_152337 78222102464075714486921 := by
  unfold tailWord_152337
  simp only [CollatzResearch.WordTrace]
  refine ⟨5556186849116540933383265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3704124566077693955588843 5556186849116540933383265)
  ·
    refine ⟨4167140136837405700037449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5556186849116540933383265 4167140136837405700037449)
    ·
      refine ⟨3125355102628054275028087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4167140136837405700037449 3125355102628054275028087)
      ·
        refine ⟨4688032653942081412542131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3125355102628054275028087 4688032653942081412542131)
        ·
          refine ⟨7032048980913122118813197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4688032653942081412542131 7032048980913122118813197)
          ·
            refine ⟨2637018367842420794554949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7032048980913122118813197 2637018367842420794554949)
            ·
              refine ⟨494440943970453898979053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2637018367842420794554949 494440943970453898979053)
              ·
                refine ⟨185415353988920212117145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 494440943970453898979053 185415353988920212117145)
                ·
                  refine ⟨139061515491690159087859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 185415353988920212117145 139061515491690159087859)
                  ·
                    refine ⟨208592273237535238631789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 139061515491690159087859 208592273237535238631789)
                    ·
                      refine ⟨78222102464075714486921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 208592273237535238631789 78222102464075714486921)
                      ·
                        rfl

theorem cell23_152337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 3, 2, 1, 3].length) (baseStart_152337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_152337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_152337 prefixEnd_152337 := by exact prefixLift 152337
  have htrace : WordTrace (prefixWord ++ tailWord_152337) baseStart_152337 baseEnd_152337 := by
    simpa [prefixWord, tailWord_152337, baseEnd_152337] using wordTrace_append hprefix tailTrace_152337
  have hstable : (prefixWord ++ tailWord_152337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152337).length < 2 ^ (prefixWord ++ tailWord_152337).sum := by decide
  have hdescent : baseEnd_152337 < baseStart_152337 := by decide
  rcases family_descends (prefixWord ++ tailWord_152337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152353 : List Nat := [1, 2, 3, 2, 1, 2, 1, 2, 1, 8]
def baseStart_152353 : Nat := 118140960795 + 152353 * 2 ^ 59
def prefixEnd_152353 : Nat := 4983230072969 + 3 ^ 40 * 152353 * 2
def baseEnd_152353 : Nat := 26076772718182550628949

theorem tailTrace_152353 : CollatzResearch.WordTrace tailWord_152353 prefixEnd_152353 26076772718182550628949 := by
  unfold tailWord_152353
  simp only [CollatzResearch.WordTrace]
  refine ⟨5556770417058575665965713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3704513611372383777310475 5556770417058575665965713)
  ·
    refine ⟨4167577812793931749474285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5556770417058575665965713 4167577812793931749474285)
    ·
      refine ⟨1562841679797724406052857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4167577812793931749474285 1562841679797724406052857)
      ·
        refine ⟨1172131259848293304539643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1562841679797724406052857 1172131259848293304539643)
        ·
          refine ⟨1758196889772439956809465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1172131259848293304539643 1758196889772439956809465)
          ·
            refine ⟨1318647667329329967607099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1758196889772439956809465 1318647667329329967607099)
            ·
              refine ⟨1977971500993994951410649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1318647667329329967607099 1977971500993994951410649)
              ·
                refine ⟨1483478625745496213557987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1977971500993994951410649 1483478625745496213557987)
                ·
                  refine ⟨2225217938618244320336981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1483478625745496213557987 2225217938618244320336981)
                  ·
                    refine ⟨26076772718182550628949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 2225217938618244320336981 26076772718182550628949)
                    ·
                      rfl

theorem cell23_152353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 8].length) (baseStart_152353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_152353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_152353 prefixEnd_152353 := by exact prefixLift 152353
  have htrace : WordTrace (prefixWord ++ tailWord_152353) baseStart_152353 baseEnd_152353 := by
    simpa [prefixWord, tailWord_152353, baseEnd_152353] using wordTrace_append hprefix tailTrace_152353
  have hstable : (prefixWord ++ tailWord_152353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152353).length < 2 ^ (prefixWord ++ tailWord_152353).sum := by decide
  have hdescent : baseEnd_152353 < baseStart_152353 := by decide
  rcases family_descends (prefixWord ++ tailWord_152353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152388 : List Nat := [2, 3, 4, 2, 2, 1, 1, 1, 1, 3, 3]
def baseStart_152388 : Nat := 118140960795 + 152388 * 2 ^ 59
def prefixEnd_152388 : Nat := 4983230072969 + 3 ^ 40 * 152388 * 2
def baseEnd_152388 : Nat := 78248289977455014949187

theorem tailTrace_152388 : CollatzResearch.WordTrace tailWord_152388 prefixEnd_152388 78248289977455014949187 := by
  unfold tailWord_152388
  simp only [CollatzResearch.WordTrace]
  refine ⟨2779023485965888321744909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3705364647954517762326545 2779023485965888321744909)
  ·
    refine ⟨1042133807237208120654341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2779023485965888321744909 1042133807237208120654341)
    ·
      refine ⟨195400088856976522622689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1042133807237208120654341 195400088856976522622689)
      ·
        refine ⟨146550066642732391967017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195400088856976522622689 146550066642732391967017)
        ·
          refine ⟨109912549982049293975263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146550066642732391967017 109912549982049293975263)
          ·
            refine ⟨164868824973073940962895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109912549982049293975263 164868824973073940962895)
            ·
              refine ⟨247303237459610911444343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164868824973073940962895 247303237459610911444343)
              ·
                refine ⟨370954856189416367166515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 247303237459610911444343 370954856189416367166515)
                ·
                  refine ⟨556432284284124550749773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 370954856189416367166515 556432284284124550749773)
                  ·
                    refine ⟨208662106606546706531165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 556432284284124550749773 208662106606546706531165)
                    ·
                      refine ⟨78248289977455014949187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 208662106606546706531165 78248289977455014949187)
                      ·
                        rfl

theorem cell23_152388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_152388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_152388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_152388 prefixEnd_152388 := by exact prefixLift 152388
  have htrace : WordTrace (prefixWord ++ tailWord_152388) baseStart_152388 baseEnd_152388 := by
    simpa [prefixWord, tailWord_152388, baseEnd_152388] using wordTrace_append hprefix tailTrace_152388
  have hstable : (prefixWord ++ tailWord_152388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152388).length < 2 ^ (prefixWord ++ tailWord_152388).sum := by decide
  have hdescent : baseEnd_152388 < baseStart_152388 := by decide
  rcases family_descends (prefixWord ++ tailWord_152388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152551 : List Nat := [1, 1, 5, 2, 2, 2, 2, 1, 3, 1, 3]
def baseStart_152551 : Nat := 118140960795 + 152551 * 2 ^ 59
def prefixEnd_152551 : Nat := 4983230072969 + 3 ^ 40 * 152551 * 2
def baseEnd_152551 : Nat := 78331987324137877210937

theorem tailTrace_152551 : CollatzResearch.WordTrace tailWord_152551 prefixEnd_152551 78331987324137877210937 := by
  unfold tailWord_152551
  simp only [CollatzResearch.WordTrace]
  refine ⟨5563992070341255481673507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3709328046894170321115671 5563992070341255481673507)
  ·
    refine ⟨8345988105511883222510261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5563992070341255481673507 8345988105511883222510261)
    ·
      refine ⟨782436384891739052110337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8345988105511883222510261 782436384891739052110337)
      ·
        refine ⟨586827288668804289082753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 782436384891739052110337 586827288668804289082753)
        ·
          refine ⟨440120466501603216812065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 586827288668804289082753 440120466501603216812065)
          ·
            refine ⟨330090349876202412609049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 440120466501603216812065 330090349876202412609049)
            ·
              refine ⟨247567762407151809456787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 330090349876202412609049 247567762407151809456787)
              ·
                refine ⟨371351643610727714185181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 247567762407151809456787 371351643610727714185181)
                ·
                  refine ⟨139256866354022892819443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 371351643610727714185181 139256866354022892819443)
                  ·
                    refine ⟨208885299531034339229165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 139256866354022892819443 208885299531034339229165)
                    ·
                      refine ⟨78331987324137877210937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 208885299531034339229165 78331987324137877210937)
                      ·
                        rfl

theorem cell23_152551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_152551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_152551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_152551 prefixEnd_152551 := by exact prefixLift 152551
  have htrace : WordTrace (prefixWord ++ tailWord_152551) baseStart_152551 baseEnd_152551 := by
    simpa [prefixWord, tailWord_152551, baseEnd_152551] using wordTrace_append hprefix tailTrace_152551
  have hstable : (prefixWord ++ tailWord_152551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152551).length < 2 ^ (prefixWord ++ tailWord_152551).sum := by decide
  have hdescent : baseEnd_152551 < baseStart_152551 := by decide
  rcases family_descends (prefixWord ++ tailWord_152551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152597 : List Nat := [1, 3, 2, 1, 4, 3, 9]
def baseStart_152597 : Nat := 118140960795 + 152597 * 2 ^ 59
def prefixEnd_152597 : Nat := 4983230072969 + 3 ^ 40 * 152597 * 2
def baseEnd_152597 : Nat := 967353178200551817725

theorem tailTrace_152597 : CollatzResearch.WordTrace tailWord_152597 prefixEnd_152597 967353178200551817725 := by
  unfold tailWord_152597
  simp only [CollatzResearch.WordTrace]
  refine ⟨5565669828174605337848045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3710446552116403558565363 5565669828174605337848045)
  ·
    refine ⟨2087126185565477001693017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5565669828174605337848045 2087126185565477001693017)
    ·
      refine ⟨1565344639174107751269763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2087126185565477001693017 1565344639174107751269763)
      ·
        refine ⟨2348016958761161626904645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1565344639174107751269763 2348016958761161626904645)
        ·
          refine ⟨440253179767717805044621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2348016958761161626904645 440253179767717805044621)
          ·
            refine ⟨165094942412894176891733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 440253179767717805044621 165094942412894176891733)
            ·
              refine ⟨967353178200551817725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 165094942412894176891733 967353178200551817725)
              ·
                rfl

theorem cell23_152597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 9].length) (baseStart_152597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_152597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_152597 prefixEnd_152597 := by exact prefixLift 152597
  have htrace : WordTrace (prefixWord ++ tailWord_152597) baseStart_152597 baseEnd_152597 := by
    simpa [prefixWord, tailWord_152597, baseEnd_152597] using wordTrace_append hprefix tailTrace_152597
  have hstable : (prefixWord ++ tailWord_152597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152597).length < 2 ^ (prefixWord ++ tailWord_152597).sum := by decide
  have hdescent : baseEnd_152597 < baseStart_152597 := by decide
  rcases family_descends (prefixWord ++ tailWord_152597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152628 : List Nat := [2, 5, 1, 2, 1, 1, 3, 2, 1, 2, 3]
def baseStart_152628 : Nat := 118140960795 + 152628 * 2 ^ 59
def prefixEnd_152628 : Nat := 4983230072969 + 3 ^ 40 * 152628 * 2
def baseEnd_152628 : Nat := 78371525334534075948083

theorem tailTrace_152628 : CollatzResearch.WordTrace tailWord_152628 prefixEnd_152628 78371525334534075948083 := by
  unfold tailWord_152628
  simp only [CollatzResearch.WordTrace]
  refine ⟨2783400245531148816113269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3711200327374865088151025 2783400245531148816113269)
  ·
    refine ⟨260943773018545201510619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2783400245531148816113269 260943773018545201510619)
    ·
      refine ⟨391415659527817802265929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260943773018545201510619 391415659527817802265929)
      ·
        refine ⟨293561744645863351699447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 391415659527817802265929 293561744645863351699447)
        ·
          refine ⟨440342616968795027549171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293561744645863351699447 440342616968795027549171)
          ·
            refine ⟨660513925453192541323757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 440342616968795027549171 660513925453192541323757)
            ·
              refine ⟨247692722044947202996409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 660513925453192541323757 247692722044947202996409)
              ·
                refine ⟨185769541533710402247307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 247692722044947202996409 185769541533710402247307)
                ·
                  refine ⟨278654312300565603370961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 185769541533710402247307 278654312300565603370961)
                  ·
                    refine ⟨208990734225424202528221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 278654312300565603370961 208990734225424202528221)
                    ·
                      refine ⟨78371525334534075948083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 208990734225424202528221 78371525334534075948083)
                      ·
                        rfl

theorem cell23_152628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_152628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_152628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_152628 prefixEnd_152628 := by exact prefixLift 152628
  have htrace : WordTrace (prefixWord ++ tailWord_152628) baseStart_152628 baseEnd_152628 := by
    simpa [prefixWord, tailWord_152628, baseEnd_152628] using wordTrace_append hprefix tailTrace_152628
  have hstable : (prefixWord ++ tailWord_152628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152628).length < 2 ^ (prefixWord ++ tailWord_152628).sum := by decide
  have hdescent : baseEnd_152628 < baseStart_152628 := by decide
  rcases family_descends (prefixWord ++ tailWord_152628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152641 : List Nat := [1, 2, 5, 1, 3, 1, 1, 2, 1, 3, 3]
def baseStart_152641 : Nat := 118140960795 + 152641 * 2 ^ 59
def prefixEnd_152641 : Nat := 4983230072969 + 3 ^ 40 * 152641 * 2
def baseEnd_152641 : Nat := 78378200583042525085523

theorem tailTrace_152641 : CollatzResearch.WordTrace tailWord_152641 prefixEnd_152641 78378200583042525085523 := by
  unfold tailWord_152641
  simp only [CollatzResearch.WordTrace]
  refine ⟨5567274640015200852449777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3711516426676800568299851 5567274640015200852449777)
  ·
    refine ⟨4175455980011400639337333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5567274640015200852449777 4175455980011400639337333)
    ·
      refine ⟨391448998126068809937875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4175455980011400639337333 391448998126068809937875)
      ·
        refine ⟨587173497189103214906813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 391448998126068809937875 587173497189103214906813)
        ·
          refine ⟨220190061445913705590055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 587173497189103214906813 220190061445913705590055)
          ·
            refine ⟨330285092168870558385083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220190061445913705590055 330285092168870558385083)
            ·
              refine ⟨495427638253305837577625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 330285092168870558385083 495427638253305837577625)
              ·
                refine ⟨371570728689979378183219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 495427638253305837577625 371570728689979378183219)
                ·
                  refine ⟨557356093034969067274829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 371570728689979378183219 557356093034969067274829)
                  ·
                    refine ⟨209008534888113400228061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 557356093034969067274829 209008534888113400228061)
                    ·
                      refine ⟨78378200583042525085523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 209008534888113400228061 78378200583042525085523)
                      ·
                        rfl

theorem cell23_152641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_152641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_152641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_152641 prefixEnd_152641 := by exact prefixLift 152641
  have htrace : WordTrace (prefixWord ++ tailWord_152641) baseStart_152641 baseEnd_152641 := by
    simpa [prefixWord, tailWord_152641, baseEnd_152641] using wordTrace_append hprefix tailTrace_152641
  have hstable : (prefixWord ++ tailWord_152641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152641).length < 2 ^ (prefixWord ++ tailWord_152641).sum := by decide
  have hdescent : baseEnd_152641 < baseStart_152641 := by decide
  rcases family_descends (prefixWord ++ tailWord_152641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152658 : List Nat := [3, 2, 2, 1, 3, 2, 2, 2, 2, 1, 3]
def baseStart_152658 : Nat := 118140960795 + 152658 * 2 ^ 59
def prefixEnd_152658 : Nat := 4983230072969 + 3 ^ 40 * 152658 * 2
def baseEnd_152658 : Nat := 78386929754168958572945

theorem tailTrace_152658 : CollatzResearch.WordTrace tailWord_152658 prefixEnd_152658 78386929754168958572945 := by
  unfold tailWord_152658
  simp only [CollatzResearch.WordTrace]
  refine ⟨1391973670238403188954657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3711929787302408503879085 1391973670238403188954657)
  ·
    refine ⟨1043980252678802391715993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1391973670238403188954657 1043980252678802391715993)
    ·
      refine ⟨782985189509101793786995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1043980252678802391715993 782985189509101793786995)
      ·
        refine ⟨1174477784263652690680493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 782985189509101793786995 1174477784263652690680493)
        ·
          refine ⟨440429169098869759005185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1174477784263652690680493 440429169098869759005185)
          ·
            refine ⟨330321876824152319253889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 440429169098869759005185 330321876824152319253889)
            ·
              refine ⟨247741407618114239440417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 330321876824152319253889 247741407618114239440417)
              ·
                refine ⟨185806055713585679580313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 247741407618114239440417 185806055713585679580313)
                ·
                  refine ⟨139354541785189259685235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 185806055713585679580313 139354541785189259685235)
                  ·
                    refine ⟨209031812677783889527853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 139354541785189259685235 209031812677783889527853)
                    ·
                      refine ⟨78386929754168958572945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 209031812677783889527853 78386929754168958572945)
                      ·
                        rfl

theorem cell23_152658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_152658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_152658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_152658 prefixEnd_152658 := by exact prefixLift 152658
  have htrace : WordTrace (prefixWord ++ tailWord_152658) baseStart_152658 baseEnd_152658 := by
    simpa [prefixWord, tailWord_152658, baseEnd_152658] using wordTrace_append hprefix tailTrace_152658
  have hstable : (prefixWord ++ tailWord_152658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152658).length < 2 ^ (prefixWord ++ tailWord_152658).sum := by decide
  have hdescent : baseEnd_152658 < baseStart_152658 := by decide
  rcases family_descends (prefixWord ++ tailWord_152658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152664 : List Nat := [2, 1, 2, 2, 1, 3, 1, 2, 3, 4, 2]
def baseStart_152664 : Nat := 118140960795 + 152664 * 2 ^ 59
def prefixEnd_152664 : Nat := 4983230072969 + 3 ^ 40 * 152664 * 2
def baseEnd_152664 : Nat := 78390010638095935097917

theorem tailTrace_152664 : CollatzResearch.WordTrace tailWord_152664 prefixEnd_152664 78390010638095935097917 := by
  unfold tailWord_152664
  simp only [CollatzResearch.WordTrace]
  refine ⟨2784056759465937890268523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3712075679287917187024697 2784056759465937890268523)
  ·
    refine ⟨4176085139198906835402785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2784056759465937890268523 4176085139198906835402785)
    ·
      refine ⟨3132063854399180126552089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4176085139198906835402785 3132063854399180126552089)
      ·
        refine ⟨2349047890799385094914067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3132063854399180126552089 2349047890799385094914067)
        ·
          refine ⟨3523571836199077642371101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2349047890799385094914067 3523571836199077642371101)
          ·
            refine ⟨1321339438574654115889163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3523571836199077642371101 1321339438574654115889163)
            ·
              refine ⟨1982009157861981173833745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1321339438574654115889163 1982009157861981173833745)
              ·
                refine ⟨1486506868396485880375309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1982009157861981173833745 1486506868396485880375309)
                ·
                  refine ⟨557440075648682205140741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1486506868396485880375309 557440075648682205140741)
                  ·
                    refine ⟨104520014184127913463889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 557440075648682205140741 104520014184127913463889)
                    ·
                      refine ⟨78390010638095935097917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 104520014184127913463889 78390010638095935097917)
                      ·
                        rfl

theorem cell23_152664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 3, 4, 2].length) (baseStart_152664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_152664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_152664 prefixEnd_152664 := by exact prefixLift 152664
  have htrace : WordTrace (prefixWord ++ tailWord_152664) baseStart_152664 baseEnd_152664 := by
    simpa [prefixWord, tailWord_152664, baseEnd_152664] using wordTrace_append hprefix tailTrace_152664
  have hstable : (prefixWord ++ tailWord_152664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152664).length < 2 ^ (prefixWord ++ tailWord_152664).sum := by decide
  have hdescent : baseEnd_152664 < baseStart_152664 := by decide
  rcases family_descends (prefixWord ++ tailWord_152664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152674 : List Nat := [3, 3, 2, 2, 1, 1, 1, 1, 1, 8]
def baseStart_152674 : Nat := 118140960795 + 152674 * 2 ^ 59
def prefixEnd_152674 : Nat := 4983230072969 + 3 ^ 40 * 152674 * 2
def baseEnd_152674 : Nat := 26131715148213631990957

theorem tailTrace_152674 : CollatzResearch.WordTrace tailWord_152674 prefixEnd_152674 26131715148213631990957 := by
  unfold tailWord_152674
  simp only [CollatzResearch.WordTrace]
  refine ⟨1392119562223911872100269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3712318832597098325600717 1392119562223911872100269)
  ·
    refine ⟨522044835833966952037601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1392119562223911872100269 522044835833966952037601)
    ·
      refine ⟨391533626875475214028201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 522044835833966952037601 391533626875475214028201)
      ·
        refine ⟨293650220156606410521151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 391533626875475214028201 293650220156606410521151)
        ·
          refine ⟨440475330234909615781727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293650220156606410521151 440475330234909615781727)
          ·
            refine ⟨660712995352364423672591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 440475330234909615781727 660712995352364423672591)
            ·
              refine ⟨991069493028546635508887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 660712995352364423672591 991069493028546635508887)
              ·
                refine ⟨1486604239542819953263331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 991069493028546635508887 1486604239542819953263331)
                ·
                  refine ⟨2229906359314229929894997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1486604239542819953263331 2229906359314229929894997)
                  ·
                    refine ⟨26131715148213631990957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 2229906359314229929894997 26131715148213631990957)
                    ·
                      rfl

theorem cell23_152674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_152674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_152674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_152674 prefixEnd_152674 := by exact prefixLift 152674
  have htrace : WordTrace (prefixWord ++ tailWord_152674) baseStart_152674 baseEnd_152674 := by
    simpa [prefixWord, tailWord_152674, baseEnd_152674] using wordTrace_append hprefix tailTrace_152674
  have hstable : (prefixWord ++ tailWord_152674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152674).length < 2 ^ (prefixWord ++ tailWord_152674).sum := by decide
  have hdescent : baseEnd_152674 < baseStart_152674 := by decide
  rcases family_descends (prefixWord ++ tailWord_152674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152681 : List Nat := [1, 2, 1, 1, 1, 7, 2, 1, 1, 4, 2]
def baseStart_152681 : Nat := 118140960795 + 152681 * 2 ^ 59
def prefixEnd_152681 : Nat := 4983230072969 + 3 ^ 40 * 152681 * 2
def baseEnd_152681 : Nat := 78398739809222368585339

theorem tailTrace_152681 : CollatzResearch.WordTrace tailWord_152681 prefixEnd_152681 78398739809222368585339 := by
  unfold tailWord_152681
  simp only [CollatzResearch.WordTrace]
  refine ⟨5568733559870287683905897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3712489039913525122603931 5568733559870287683905897)
  ·
    refine ⟨4176550169902715762929423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5568733559870287683905897 4176550169902715762929423)
    ·
      refine ⟨6264825254854073644394135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4176550169902715762929423 6264825254854073644394135)
      ·
        refine ⟨9397237882281110466591203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6264825254854073644394135 9397237882281110466591203)
        ·
          refine ⟨14095856823421665699886805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9397237882281110466591203 14095856823421665699886805)
          ·
            refine ⟨330371644298945289841097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 14095856823421665699886805 330371644298945289841097)
            ·
              refine ⟨247778733224208967380823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 330371644298945289841097 247778733224208967380823)
              ·
                refine ⟨371668099836313451071235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 247778733224208967380823 371668099836313451071235)
                ·
                  refine ⟨557502149754470176606853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 371668099836313451071235 557502149754470176606853)
                  ·
                    refine ⟨104531653078963158113785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 557502149754470176606853 104531653078963158113785)
                    ·
                      refine ⟨78398739809222368585339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 104531653078963158113785 78398739809222368585339)
                      ·
                        rfl

theorem cell23_152681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 4, 2].length) (baseStart_152681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_152681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_152681 prefixEnd_152681 := by exact prefixLift 152681
  have htrace : WordTrace (prefixWord ++ tailWord_152681) baseStart_152681 baseEnd_152681 := by
    simpa [prefixWord, tailWord_152681, baseEnd_152681] using wordTrace_append hprefix tailTrace_152681
  have hstable : (prefixWord ++ tailWord_152681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152681).length < 2 ^ (prefixWord ++ tailWord_152681).sum := by decide
  have hdescent : baseEnd_152681 < baseStart_152681 := by decide
  rcases family_descends (prefixWord ++ tailWord_152681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152687 : List Nat := [1, 1, 2, 1, 3, 3, 3, 2, 7]
def baseStart_152687 : Nat := 118140960795 + 152687 * 2 ^ 59
def prefixEnd_152687 : Nat := 4983230072969 + 3 ^ 40 * 152687 * 2
def baseEnd_152687 : Nat := 8711313410349927234479

theorem tailTrace_152687 : CollatzResearch.WordTrace tailWord_152687 prefixEnd_152687 8711313410349927234479 := by
  unfold tailWord_152687
  simp only [CollatzResearch.WordTrace]
  refine ⟨5568952397848550708624315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3712634931899033805749543 5568952397848550708624315)
  ·
    refine ⟨8353428596772826062936473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5568952397848550708624315 8353428596772826062936473)
    ·
      refine ⟨6265071447579619547202355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8353428596772826062936473 6265071447579619547202355)
      ·
        refine ⟨9397607171369429320803533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6265071447579619547202355 9397607171369429320803533)
        ·
          refine ⟨3524102689263535995301325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9397607171369429320803533 3524102689263535995301325)
          ·
            refine ⟨1321538508473825998237997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3524102689263535995301325 1321538508473825998237997)
            ·
              refine ⟨495576940677684749339249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1321538508473825998237997 495576940677684749339249)
              ·
                refine ⟨371682705508263562004437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 495576940677684749339249 371682705508263562004437)
                ·
                  refine ⟨8711313410349927234479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 371682705508263562004437 8711313410349927234479)
                  ·
                    rfl

theorem cell23_152687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 7].length) (baseStart_152687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_152687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_152687 prefixEnd_152687 := by exact prefixLift 152687
  have htrace : WordTrace (prefixWord ++ tailWord_152687) baseStart_152687 baseEnd_152687 := by
    simpa [prefixWord, tailWord_152687, baseEnd_152687] using wordTrace_append hprefix tailTrace_152687
  have hstable : (prefixWord ++ tailWord_152687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152687).length < 2 ^ (prefixWord ++ tailWord_152687).sum := by decide
  have hdescent : baseEnd_152687 < baseStart_152687 := by decide
  rcases family_descends (prefixWord ++ tailWord_152687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152694 : List Nat := [5, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4]
def baseStart_152694 : Nat := 118140960795 + 152694 * 2 ^ 59
def prefixEnd_152694 : Nat := 4983230072969 + 3 ^ 40 * 152694 * 2
def baseEnd_152694 : Nat := 78405415057730817722779

theorem tailTrace_152694 : CollatzResearch.WordTrace tailWord_152694 prefixEnd_152694 78405415057730817722779 := by
  unfold tailWord_152694
  simp only [CollatzResearch.WordTrace]
  refine ⟨348075481801449431508071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3712805139215460602752757 348075481801449431508071)
  ·
    refine ⟨522113222702174147262107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 348075481801449431508071 522113222702174147262107)
    ·
      refine ⟨783169834053261220893161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 522113222702174147262107 783169834053261220893161)
      ·
        refine ⟨587377375539945915669871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 783169834053261220893161 587377375539945915669871)
        ·
          refine ⟨881066063309918873504807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 587377375539945915669871 881066063309918873504807)
          ·
            refine ⟨1321599094964878310257211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 881066063309918873504807 1321599094964878310257211)
            ·
              refine ⟨1982398642447317465385817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1321599094964878310257211 1982398642447317465385817)
              ·
                refine ⟨1486798981835488099039363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1982398642447317465385817 1486798981835488099039363)
                ·
                  refine ⟨2230198472753232148559045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1486798981835488099039363 2230198472753232148559045)
                  ·
                    refine ⟨418162213641231027854821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2230198472753232148559045 418162213641231027854821)
                    ·
                      refine ⟨78405415057730817722779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 418162213641231027854821 78405415057730817722779)
                      ·
                        rfl

theorem cell23_152694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_152694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_152694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_152694 prefixEnd_152694 := by exact prefixLift 152694
  have htrace : WordTrace (prefixWord ++ tailWord_152694) baseStart_152694 baseEnd_152694 := by
    simpa [prefixWord, tailWord_152694, baseEnd_152694] using wordTrace_append hprefix tailTrace_152694
  have hstable : (prefixWord ++ tailWord_152694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152694).length < 2 ^ (prefixWord ++ tailWord_152694).sum := by decide
  have hdescent : baseEnd_152694 < baseStart_152694 := by decide
  rcases family_descends (prefixWord ++ tailWord_152694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152704 : List Nat := [2, 1, 1, 2, 1, 3, 3, 5, 5]
def baseStart_152704 : Nat := 118140960795 + 152704 * 2 ^ 59
def prefixEnd_152704 : Nat := 4983230072969 + 3 ^ 40 * 152704 * 2
def baseEnd_152704 : Nat := 8712283318252864288637

theorem tailTrace_152704 : CollatzResearch.WordTrace tailWord_152704 prefixEnd_152704 8712283318252864288637 := by
  unfold tailWord_152704
  simp only [CollatzResearch.WordTrace]
  refine ⟨2784786219393481305996583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3713048292524641741328777 2784786219393481305996583)
  ·
    refine ⟨4177179329090221958994875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2784786219393481305996583 4177179329090221958994875)
    ·
      refine ⟨6265768993635332938492313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4177179329090221958994875 6265768993635332938492313)
      ·
        refine ⟨4699326745226499703869235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6265768993635332938492313 4699326745226499703869235)
        ·
          refine ⟨7048990117839749555803853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4699326745226499703869235 7048990117839749555803853)
          ·
            refine ⟨2643371294189906083426445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7048990117839749555803853 2643371294189906083426445)
            ·
              refine ⟨991264235321214781284917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2643371294189906083426445 991264235321214781284917)
              ·
                refine ⟨92931022061363885745461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 991264235321214781284917 92931022061363885745461)
                ·
                  refine ⟨8712283318252864288637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 92931022061363885745461 8712283318252864288637)
                  ·
                    rfl

theorem cell23_152704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 5, 5].length) (baseStart_152704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_152704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_152704 prefixEnd_152704 := by exact prefixLift 152704
  have htrace : WordTrace (prefixWord ++ tailWord_152704) baseStart_152704 baseEnd_152704 := by
    simpa [prefixWord, tailWord_152704, baseEnd_152704] using wordTrace_append hprefix tailTrace_152704
  have hstable : (prefixWord ++ tailWord_152704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152704).length < 2 ^ (prefixWord ++ tailWord_152704).sum := by decide
  have hdescent : baseEnd_152704 < baseStart_152704 := by decide
  rcases family_descends (prefixWord ++ tailWord_152704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152714 : List Nat := [3, 1, 2, 3, 1, 1, 1, 1, 4, 3, 3]
def baseStart_152714 : Nat := 118140960795 + 152714 * 2 ^ 59
def prefixEnd_152714 : Nat := 4983230072969 + 3 ^ 40 * 152714 * 2
def baseEnd_152714 : Nat := 78415684670820739472687

theorem tailTrace_152714 : CollatzResearch.WordTrace tailWord_152714 prefixEnd_152714 78415684670820739472687 := by
  unfold tailWord_152714
  simp only [CollatzResearch.WordTrace]
  refine ⟨1392484292187683579964299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3713291445833822879904797 1392484292187683579964299)
  ·
    refine ⟨2088726438281525369946449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1392484292187683579964299 2088726438281525369946449)
    ·
      refine ⟨1566544828711144027459837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2088726438281525369946449 1566544828711144027459837)
      ·
        refine ⟨587454310766679010297439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1566544828711144027459837 587454310766679010297439)
        ·
          refine ⟨881181466150018515446159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 587454310766679010297439 881181466150018515446159)
          ·
            refine ⟨1321772199225027773169239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 881181466150018515446159 1321772199225027773169239)
            ·
              refine ⟨1982658298837541659753859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1321772199225027773169239 1982658298837541659753859)
              ·
                refine ⟨2973987448256312489630789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1982658298837541659753859 2973987448256312489630789)
                ·
                  refine ⟨557622646548058591805773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2973987448256312489630789 557622646548058591805773)
                  ·
                    refine ⟨209108492455521971927165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 557622646548058591805773 209108492455521971927165)
                    ·
                      refine ⟨78415684670820739472687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 209108492455521971927165 78415684670820739472687)
                      ·
                        rfl

theorem cell23_152714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_152714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_152714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_152714 prefixEnd_152714 := by exact prefixLift 152714
  have htrace : WordTrace (prefixWord ++ tailWord_152714) baseStart_152714 baseEnd_152714 := by
    simpa [prefixWord, tailWord_152714, baseEnd_152714] using wordTrace_append hprefix tailTrace_152714
  have hstable : (prefixWord ++ tailWord_152714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152714).length < 2 ^ (prefixWord ++ tailWord_152714).sum := by decide
  have hdescent : baseEnd_152714 < baseStart_152714 := by decide
  rcases family_descends (prefixWord ++ tailWord_152714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152754 : List Nat := [3, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4]
def baseStart_152754 : Nat := 118140960795 + 152754 * 2 ^ 59
def prefixEnd_152754 : Nat := 4983230072969 + 3 ^ 40 * 152754 * 2
def baseEnd_152754 : Nat := 78436223897000582972503

theorem tailTrace_152754 : CollatzResearch.WordTrace tailWord_152754 prefixEnd_152754 78436223897000582972503 := by
  unfold tailWord_152754
  simp only [CollatzResearch.WordTrace]
  refine ⟨1392849022151455287828329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3714264059070547434208877 1392849022151455287828329)
  ·
    refine ⟨1044636766613591465871247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1392849022151455287828329 1044636766613591465871247)
    ·
      refine ⟨1566955149920387198806871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1044636766613591465871247 1566955149920387198806871)
      ·
        refine ⟨2350432724880580798210307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1566955149920387198806871 2350432724880580798210307)
        ·
          refine ⟨3525649087320871197315461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2350432724880580798210307 3525649087320871197315461)
          ·
            refine ⟨661059203872663349496649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3525649087320871197315461 661059203872663349496649)
            ·
              refine ⟨495794402904497512122487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 661059203872663349496649 495794402904497512122487)
              ·
                refine ⟨743691604356746268183731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 495794402904497512122487 743691604356746268183731)
                ·
                  refine ⟨1115537406535119402275597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 743691604356746268183731 1115537406535119402275597)
                  ·
                    refine ⟨418326527450669775853349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1115537406535119402275597 418326527450669775853349)
                    ·
                      refine ⟨78436223897000582972503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 418326527450669775853349 78436223897000582972503)
                      ·
                        rfl

theorem cell23_152754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_152754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_152754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_152754 prefixEnd_152754 := by exact prefixLift 152754
  have htrace : WordTrace (prefixWord ++ tailWord_152754) baseStart_152754 baseEnd_152754 := by
    simpa [prefixWord, tailWord_152754, baseEnd_152754] using wordTrace_append hprefix tailTrace_152754
  have hstable : (prefixWord ++ tailWord_152754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152754).length < 2 ^ (prefixWord ++ tailWord_152754).sum := by decide
  have hdescent : baseEnd_152754 < baseStart_152754 := by decide
  rcases family_descends (prefixWord ++ tailWord_152754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152767 : List Nat := [1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 6]
def baseStart_152767 : Nat := 118140960795 + 152767 * 2 ^ 59
def prefixEnd_152767 : Nat := 4983230072969 + 3 ^ 40 * 152767 * 2
def baseEnd_152767 : Nat := 78442899145509032109943

theorem tailTrace_152767 : CollatzResearch.WordTrace tailWord_152767 prefixEnd_152767 78442899145509032109943 := by
  unfold tailWord_152767
  simp only [CollatzResearch.WordTrace]
  refine ⟨5571870237558724371536555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3714580158372482914357703 5571870237558724371536555)
  ·
    refine ⟨8357805356338086557304833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5571870237558724371536555 8357805356338086557304833)
    ·
      refine ⟨6268354017253564917978625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8357805356338086557304833 6268354017253564917978625)
      ·
        refine ⟨4701265512940173688483969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6268354017253564917978625 4701265512940173688483969)
        ·
          refine ⟨3525949134705130266362977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4701265512940173688483969 3525949134705130266362977)
          ·
            refine ⟨2644461851028847699772233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3525949134705130266362977 2644461851028847699772233)
            ·
              refine ⟨1983346388271635774829175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2644461851028847699772233 1983346388271635774829175)
              ·
                refine ⟨2975019582407453662243763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1983346388271635774829175 2975019582407453662243763)
                ·
                  refine ⟨4462529373611180493365645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2975019582407453662243763 4462529373611180493365645)
                  ·
                    refine ⟨1673448515104192685012117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4462529373611180493365645 1673448515104192685012117)
                    ·
                      refine ⟨78442899145509032109943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1673448515104192685012117 78442899145509032109943)
                      ·
                        rfl

theorem cell23_152767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 6].length) (baseStart_152767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_152767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_152767 prefixEnd_152767 := by exact prefixLift 152767
  have htrace : WordTrace (prefixWord ++ tailWord_152767) baseStart_152767 baseEnd_152767 := by
    simpa [prefixWord, tailWord_152767, baseEnd_152767] using wordTrace_append hprefix tailTrace_152767
  have hstable : (prefixWord ++ tailWord_152767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152767).length < 2 ^ (prefixWord ++ tailWord_152767).sum := by decide
  have hdescent : baseEnd_152767 < baseStart_152767 := by decide
  rcases family_descends (prefixWord ++ tailWord_152767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152804 : List Nat := [2, 3, 1, 1, 1, 2, 2, 1, 2, 5, 3]
def baseStart_152804 : Nat := 118140960795 + 152804 * 2 ^ 59
def prefixEnd_152804 : Nat := 4983230072969 + 3 ^ 40 * 152804 * 2
def baseEnd_152804 : Nat := 78461897929725387347273

theorem tailTrace_152804 : CollatzResearch.WordTrace tailWord_152804 prefixEnd_152804 78461897929725387347273 := by
  unfold tailWord_152804
  simp only [CollatzResearch.WordTrace]
  refine ⟨2786609869212339845316733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3715479825616453127088977 2786609869212339845316733)
  ·
    refine ⟨1044978700954627441993775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2786609869212339845316733 1044978700954627441993775)
    ·
      refine ⟨1567468051431941162990663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1044978700954627441993775 1567468051431941162990663)
      ·
        refine ⟨2351202077147911744485995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1567468051431941162990663 2351202077147911744485995)
        ·
          refine ⟨3526803115721867616728993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2351202077147911744485995 3526803115721867616728993)
          ·
            refine ⟨2645102336791400712546745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3526803115721867616728993 2645102336791400712546745)
            ·
              refine ⟨1983826752593550534410059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2645102336791400712546745 1983826752593550534410059)
              ·
                refine ⟨2975740128890325801615089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1983826752593550534410059 2975740128890325801615089)
                ·
                  refine ⟨2231805096667744351211317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2975740128890325801615089 2231805096667744351211317)
                  ·
                    refine ⟨209231727812601032926061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2231805096667744351211317 209231727812601032926061)
                    ·
                      refine ⟨78461897929725387347273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 209231727812601032926061 78461897929725387347273)
                      ·
                        rfl

theorem cell23_152804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 2, 5, 3].length) (baseStart_152804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_152804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_152804 prefixEnd_152804 := by exact prefixLift 152804
  have htrace : WordTrace (prefixWord ++ tailWord_152804) baseStart_152804 baseEnd_152804 := by
    simpa [prefixWord, tailWord_152804, baseEnd_152804] using wordTrace_append hprefix tailTrace_152804
  have hstable : (prefixWord ++ tailWord_152804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152804).length < 2 ^ (prefixWord ++ tailWord_152804).sum := by decide
  have hdescent : baseEnd_152804 < baseStart_152804 := by decide
  rcases family_descends (prefixWord ++ tailWord_152804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152872 : List Nat := [2, 1, 5, 1, 2, 2, 2, 3, 1, 1, 3]
def baseStart_152872 : Nat := 118140960795 + 152872 * 2 ^ 59
def prefixEnd_152872 : Nat := 4983230072969 + 3 ^ 40 * 152872 * 2
def baseEnd_152872 : Nat := 78496814614231121296961

theorem tailTrace_152872 : CollatzResearch.WordTrace tailWord_152872 prefixEnd_152872 78496814614231121296961 := by
  unfold tailWord_152872
  simp only [CollatzResearch.WordTrace]
  refine ⟨2787849951089163652054435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3717133268118884869405913 2787849951089163652054435)
  ·
    refine ⟨4181774926633745478081653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2787849951089163652054435 4181774926633745478081653)
    ·
      refine ⟨392041399371913638570155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4181774926633745478081653 392041399371913638570155)
      ·
        refine ⟨588062099057870457855233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 392041399371913638570155 588062099057870457855233)
        ·
          refine ⟨441046574293402843391425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 588062099057870457855233 441046574293402843391425)
          ·
            refine ⟨330784930720052132543569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 441046574293402843391425 330784930720052132543569)
            ·
              refine ⟨248088698040039099407677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 330784930720052132543569 248088698040039099407677)
              ·
                refine ⟨93033261765014662277879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 248088698040039099407677 93033261765014662277879)
                ·
                  refine ⟨139549892647521993416819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93033261765014662277879 139549892647521993416819)
                  ·
                    refine ⟨209324838971282990125229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 139549892647521993416819 209324838971282990125229)
                    ·
                      refine ⟨78496814614231121296961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 209324838971282990125229 78496814614231121296961)
                      ·
                        rfl

theorem cell23_152872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_152872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_152872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_152872 prefixEnd_152872 := by exact prefixLift 152872
  have htrace : WordTrace (prefixWord ++ tailWord_152872) baseStart_152872 baseEnd_152872 := by
    simpa [prefixWord, tailWord_152872, baseEnd_152872] using wordTrace_append hprefix tailTrace_152872
  have hstable : (prefixWord ++ tailWord_152872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152872).length < 2 ^ (prefixWord ++ tailWord_152872).sum := by decide
  have hdescent : baseEnd_152872 < baseStart_152872 := by decide
  rcases family_descends (prefixWord ++ tailWord_152872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152895 : List Nat := [1, 1, 2, 2, 4, 3, 2, 1, 3, 2, 2]
def baseStart_152895 : Nat := 118140960795 + 152895 * 2 ^ 59
def prefixEnd_152895 : Nat := 4983230072969 + 3 ^ 40 * 152895 * 2
def baseEnd_152895 : Nat := 78508624669284531309355

theorem tailTrace_152895 : CollatzResearch.WordTrace tailWord_152895 prefixEnd_152895 78508624669284531309355 := by
  unfold tailWord_152895
  simp only [CollatzResearch.WordTrace]
  refine ⟨5576538781095002232196139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3717692520730001488130759 5576538781095002232196139)
  ·
    refine ⟨8364808171642503348294209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5576538781095002232196139 8364808171642503348294209)
    ·
      refine ⟨6273606128731877511220657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8364808171642503348294209 6273606128731877511220657)
      ·
        refine ⟨4705204596548908133415493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6273606128731877511220657 4705204596548908133415493)
        ·
          refine ⟨882225861852920275015405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4705204596548908133415493 882225861852920275015405)
          ·
            refine ⟨330834698194845103130777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 882225861852920275015405 330834698194845103130777)
            ·
              refine ⟨248126023646133827348083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 330834698194845103130777 248126023646133827348083)
              ·
                refine ⟨372189035469200741022125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 248126023646133827348083 372189035469200741022125)
                ·
                  refine ⟨139570888300950277883297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 372189035469200741022125 139570888300950277883297)
                  ·
                    refine ⟨104678166225712708412473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 139570888300950277883297 104678166225712708412473)
                    ·
                      refine ⟨78508624669284531309355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 104678166225712708412473 78508624669284531309355)
                      ·
                        rfl

theorem cell23_152895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 3, 2, 2].length) (baseStart_152895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_152895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_152895 prefixEnd_152895 := by exact prefixLift 152895
  have htrace : WordTrace (prefixWord ++ tailWord_152895) baseStart_152895 baseEnd_152895 := by
    simpa [prefixWord, tailWord_152895, baseEnd_152895] using wordTrace_append hprefix tailTrace_152895
  have hstable : (prefixWord ++ tailWord_152895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152895).length < 2 ^ (prefixWord ++ tailWord_152895).sum := by decide
  have hdescent : baseEnd_152895 < baseStart_152895 := by decide
  rcases family_descends (prefixWord ++ tailWord_152895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152908 : List Nat := [2, 2, 1, 3, 2, 4, 1, 1, 1, 2, 4]
def baseStart_152908 : Nat := 118140960795 + 152908 * 2 ^ 59
def prefixEnd_152908 : Nat := 4983230072969 + 3 ^ 40 * 152908 * 2
def baseEnd_152908 : Nat := 78515299917792980446795

theorem tailTrace_152908 : CollatzResearch.WordTrace tailWord_152908 prefixEnd_152908 78515299917792980446795 := by
  unfold tailWord_152908
  simp only [CollatzResearch.WordTrace]
  refine ⟨2788506465023952726209689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3718008620031936968279585 2788506465023952726209689)
  ·
    refine ⟨2091379848767964544657267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2788506465023952726209689 2091379848767964544657267)
    ·
      refine ⟨3137069773151946816985901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2091379848767964544657267 3137069773151946816985901)
      ·
        refine ⟨1176401164931980056369713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3137069773151946816985901 1176401164931980056369713)
        ·
          refine ⟨882300873698985042277285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1176401164931980056369713 882300873698985042277285)
          ·
            refine ⟨165431413818559695426991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 882300873698985042277285 165431413818559695426991)
            ·
              refine ⟨248147120727839543140487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165431413818559695426991 248147120727839543140487)
              ·
                refine ⟨372220681091759314710731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 248147120727839543140487 372220681091759314710731)
                ·
                  refine ⟨558331021637638972066097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 372220681091759314710731 558331021637638972066097)
                  ·
                    refine ⟨418748266228229229049573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 558331021637638972066097 418748266228229229049573)
                    ·
                      refine ⟨78515299917792980446795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 418748266228229229049573 78515299917792980446795)
                      ·
                        rfl

theorem cell23_152908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_152908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_152908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_152908 prefixEnd_152908 := by exact prefixLift 152908
  have htrace : WordTrace (prefixWord ++ tailWord_152908) baseStart_152908 baseEnd_152908 := by
    simpa [prefixWord, tailWord_152908, baseEnd_152908] using wordTrace_append hprefix tailTrace_152908
  have hstable : (prefixWord ++ tailWord_152908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152908).length < 2 ^ (prefixWord ++ tailWord_152908).sum := by decide
  have hdescent : baseEnd_152908 < baseStart_152908 := by decide
  rcases family_descends (prefixWord ++ tailWord_152908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152928 : List Nat := [2, 1, 1, 3, 4, 1, 1, 2, 4, 1, 3]
def baseStart_152928 : Nat := 118140960795 + 152928 * 2 ^ 59
def prefixEnd_152928 : Nat := 4983230072969 + 3 ^ 40 * 152928 * 2
def baseEnd_152928 : Nat := 78525569530882902196703

theorem tailTrace_152928 : CollatzResearch.WordTrace tailWord_152928 prefixEnd_152928 78525569530882902196703 := by
  unfold tailWord_152928
  simp only [CollatzResearch.WordTrace]
  refine ⟨2788871194987724434073719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3718494926650299245431625 2788871194987724434073719)
  ·
    refine ⟨4183306792481586651110579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2788871194987724434073719 4183306792481586651110579)
    ·
      refine ⟨6274960188722379976665869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4183306792481586651110579 6274960188722379976665869)
      ·
        refine ⟨2353110070770892491249701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6274960188722379976665869 2353110070770892491249701)
        ·
          refine ⟨441208138269542342109319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2353110070770892491249701 441208138269542342109319)
          ·
            refine ⟨661812207404313513163979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 441208138269542342109319 661812207404313513163979)
            ·
              refine ⟨992718311106470269745969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 661812207404313513163979 992718311106470269745969)
              ·
                refine ⟨744538733329852702309477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 992718311106470269745969 744538733329852702309477)
                ·
                  refine ⟨139601012499347381683027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 744538733329852702309477 139601012499347381683027)
                  ·
                    refine ⟨209401518749021072524541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 139601012499347381683027 209401518749021072524541)
                    ·
                      refine ⟨78525569530882902196703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 209401518749021072524541 78525569530882902196703)
                      ·
                        rfl

theorem cell23_152928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 4, 1, 3].length) (baseStart_152928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_152928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_152928 prefixEnd_152928 := by exact prefixLift 152928
  have htrace : WordTrace (prefixWord ++ tailWord_152928) baseStart_152928 baseEnd_152928 := by
    simpa [prefixWord, tailWord_152928, baseEnd_152928] using wordTrace_append hprefix tailTrace_152928
  have hstable : (prefixWord ++ tailWord_152928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152928).length < 2 ^ (prefixWord ++ tailWord_152928).sum := by decide
  have hdescent : baseEnd_152928 < baseStart_152928 := by decide
  rcases family_descends (prefixWord ++ tailWord_152928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153021 : List Nat := [1, 4, 1, 2, 2, 1, 2, 2, 1, 7]
def baseStart_153021 : Nat := 118140960795 + 153021 * 2 ^ 59
def prefixEnd_153021 : Nat := 4983230072969 + 3 ^ 40 * 153021 * 2
def baseEnd_153021 : Nat := 26191107743917012777925

theorem tailTrace_153021 : CollatzResearch.WordTrace tailWord_153021 prefixEnd_153021 26191107743917012777925 := by
  unfold tailWord_153021
  simp only [CollatzResearch.WordTrace]
  refine ⟨5581134378638525751282917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3720756252425683834188611 5581134378638525751282917)
  ·
    refine ⟨1046462695994723578365547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5581134378638525751282917 1046462695994723578365547)
    ·
      refine ⟨1569694043992085367548321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1046462695994723578365547 1569694043992085367548321)
      ·
        refine ⟨1177270532994064025661241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1569694043992085367548321 1177270532994064025661241)
        ·
          refine ⟨882952899745548019245931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1177270532994064025661241 882952899745548019245931)
          ·
            refine ⟨1324429349618322028868897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 882952899745548019245931 1324429349618322028868897)
            ·
              refine ⟨993322012213741521651673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1324429349618322028868897 993322012213741521651673)
              ·
                refine ⟨744991509160306141238755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 993322012213741521651673 744991509160306141238755)
                ·
                  refine ⟨1117487263740459211858133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 744991509160306141238755 1117487263740459211858133)
                  ·
                    refine ⟨26191107743917012777925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1117487263740459211858133 26191107743917012777925)
                    ·
                      rfl

theorem cell23_153021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 7].length) (baseStart_153021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153021 prefixEnd_153021 := by exact prefixLift 153021
  have htrace : WordTrace (prefixWord ++ tailWord_153021) baseStart_153021 baseEnd_153021 := by
    simpa [prefixWord, tailWord_153021, baseEnd_153021] using wordTrace_append hprefix tailTrace_153021
  have hstable : (prefixWord ++ tailWord_153021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153021).length < 2 ^ (prefixWord ++ tailWord_153021).sum := by decide
  have hdescent : baseEnd_153021 < baseStart_153021 := by decide
  rcases family_descends (prefixWord ++ tailWord_153021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153038 : List Nat := [4, 1, 1, 1, 2, 1, 5, 1, 2, 5]
def baseStart_153038 : Nat := 118140960795 + 153038 * 2 ^ 59
def prefixEnd_153038 : Nat := 4983230072969 + 3 ^ 40 * 153038 * 2
def baseEnd_153038 : Nat := 26194017467625823940399

theorem tailTrace_153038 : CollatzResearch.WordTrace tailWord_153038 prefixEnd_153038 26194017467625823940399 := by
  unfold tailWord_153038
  simp only [CollatzResearch.WordTrace]
  refine ⟨697719302447117206831471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3721169613051291769767845 697719302447117206831471)
  ·
    refine ⟨1046578953670675810247207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 697719302447117206831471 1046578953670675810247207)
    ·
      refine ⟨1569868430506013715370811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1046578953670675810247207 1569868430506013715370811)
      ·
        refine ⟨2354802645759020573056217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1569868430506013715370811 2354802645759020573056217)
        ·
          refine ⟨1766101984319265429792163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2354802645759020573056217 1766101984319265429792163)
          ·
            refine ⟨2649152976478898144688245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1766101984319265429792163 2649152976478898144688245)
            ·
              refine ⟨248358091544896701064523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2649152976478898144688245 248358091544896701064523)
              ·
                refine ⟨372537137317345051596785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 248358091544896701064523 372537137317345051596785)
                ·
                  refine ⟨279402852988008788697589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 372537137317345051596785 279402852988008788697589)
                  ·
                    refine ⟨26194017467625823940399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 279402852988008788697589 26194017467625823940399)
                    ·
                      rfl

theorem cell23_153038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 1, 2, 5].length) (baseStart_153038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153038 prefixEnd_153038 := by exact prefixLift 153038
  have htrace : WordTrace (prefixWord ++ tailWord_153038) baseStart_153038 baseEnd_153038 := by
    simpa [prefixWord, tailWord_153038, baseEnd_153038] using wordTrace_append hprefix tailTrace_153038
  have hstable : (prefixWord ++ tailWord_153038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153038).length < 2 ^ (prefixWord ++ tailWord_153038).sum := by decide
  have hdescent : baseEnd_153038 < baseStart_153038 := by decide
  rcases family_descends (prefixWord ++ tailWord_153038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153131 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 1, 7, 4]
def baseStart_153131 : Nat := 118140960795 + 153131 * 2 ^ 59
def prefixEnd_153131 : Nat := 4983230072969 + 3 ^ 40 * 153131 * 2
def baseEnd_153131 : Nat := 78629806103745607958269

theorem tailTrace_153131 : CollatzResearch.WordTrace tailWord_153131 prefixEnd_153131 78629806103745607958269 := by
  unfold tailWord_153131
  simp only [CollatzResearch.WordTrace]
  refine ⟨5585146408240014537787247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3723430938826676358524831 5585146408240014537787247)
  ·
    refine ⟨8377719612360021806680871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5585146408240014537787247 8377719612360021806680871)
    ·
      refine ⟨12566579418540032710021307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8377719612360021806680871 12566579418540032710021307)
      ·
        refine ⟨18849869127810049065031961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12566579418540032710021307 18849869127810049065031961)
        ·
          refine ⟨14137401845857536798773971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18849869127810049065031961 14137401845857536798773971)
          ·
            refine ⟨21206102768786305198160957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14137401845857536798773971 21206102768786305198160957)
            ·
              refine ⟨7952288538294864449310359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21206102768786305198160957 7952288538294864449310359)
              ·
                refine ⟨11928432807442296673965539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7952288538294864449310359 11928432807442296673965539)
                ·
                  refine ⟨17892649211163445010948309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11928432807442296673965539 17892649211163445010948309)
                  ·
                    refine ⟨419358965886643242444101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17892649211163445010948309 419358965886643242444101)
                    ·
                      refine ⟨78629806103745607958269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 419358965886643242444101 78629806103745607958269)
                      ·
                        rfl

theorem cell23_153131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 7, 4].length) (baseStart_153131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153131 prefixEnd_153131 := by exact prefixLift 153131
  have htrace : WordTrace (prefixWord ++ tailWord_153131) baseStart_153131 baseEnd_153131 := by
    simpa [prefixWord, tailWord_153131, baseEnd_153131] using wordTrace_append hprefix tailTrace_153131
  have hstable : (prefixWord ++ tailWord_153131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153131).length < 2 ^ (prefixWord ++ tailWord_153131).sum := by decide
  have hdescent : baseEnd_153131 < baseStart_153131 := by decide
  rcases family_descends (prefixWord ++ tailWord_153131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153145 : List Nat := [1, 2, 1, 5, 1, 2, 3, 2, 1, 5]
def baseStart_153145 : Nat := 118140960795 + 153145 * 2 ^ 59
def prefixEnd_153145 : Nat := 4983230072969 + 3 ^ 40 * 153145 * 2
def baseEnd_153145 : Nat := 26212331610969517727735

theorem tailTrace_153145 : CollatzResearch.WordTrace tailWord_153145 prefixEnd_153145 26212331610969517727735 := by
  unfold tailWord_153145
  simp only [CollatzResearch.WordTrace]
  refine ⟨5585657030189294928796889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3723771353459529952531259 5585657030189294928796889)
  ·
    refine ⟨4189242772641971196597667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5585657030189294928796889 4189242772641971196597667)
    ·
      refine ⟨6283864158962956794896501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4189242772641971196597667 6283864158962956794896501)
      ·
        refine ⟨589112264902777199521547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6283864158962956794896501 589112264902777199521547)
        ·
          refine ⟨883668397354165799282321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 589112264902777199521547 883668397354165799282321)
          ·
            refine ⟨662751298015624349461741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 883668397354165799282321 662751298015624349461741)
            ·
              refine ⟨248531736755859131048153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 662751298015624349461741 248531736755859131048153)
              ·
                refine ⟨186398802566894348286115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 248531736755859131048153 186398802566894348286115)
                ·
                  refine ⟨279598203850341522429173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 186398802566894348286115 279598203850341522429173)
                  ·
                    refine ⟨26212331610969517727735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 279598203850341522429173 26212331610969517727735)
                    ·
                      rfl

theorem cell23_153145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 2, 1, 5].length) (baseStart_153145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153145 prefixEnd_153145 := by exact prefixLift 153145
  have htrace : WordTrace (prefixWord ++ tailWord_153145) baseStart_153145 baseEnd_153145 := by
    simpa [prefixWord, tailWord_153145, baseEnd_153145] using wordTrace_append hprefix tailTrace_153145
  have hstable : (prefixWord ++ tailWord_153145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153145).length < 2 ^ (prefixWord ++ tailWord_153145).sum := by decide
  have hdescent : baseEnd_153145 < baseStart_153145 := by decide
  rcases family_descends (prefixWord ++ tailWord_153145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153175 : List Nat := [1, 1, 3, 2, 2, 3, 1, 4, 2, 4]
def baseStart_153175 : Nat := 118140960795 + 153175 * 2 ^ 59
def prefixEnd_153175 : Nat := 4983230072969 + 3 ^ 40 * 153175 * 2
def baseEnd_153175 : Nat := 26217466417514478602689

theorem tailTrace_153175 : CollatzResearch.WordTrace tailWord_153175 prefixEnd_153175 26217466417514478602689 := by
  unfold tailWord_153175
  simp only [CollatzResearch.WordTrace]
  refine ⟨5586751220080610052388979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3724500813387073368259319 5586751220080610052388979)
  ·
    refine ⟨8380126830120915078583469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5586751220080610052388979 8380126830120915078583469)
    ·
      refine ⟨3142547561295343154468801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8380126830120915078583469 3142547561295343154468801)
      ·
        refine ⟨2356910670971507365851601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3142547561295343154468801 2356910670971507365851601)
        ·
          refine ⟨1767683003228630524388701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2356910670971507365851601 1767683003228630524388701)
          ·
            refine ⟨662881126210736446645763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1767683003228630524388701 662881126210736446645763)
            ·
              refine ⟨994321689316104669968645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 662881126210736446645763 994321689316104669968645)
              ·
                refine ⟨186435316746769625619121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 994321689316104669968645 186435316746769625619121)
                ·
                  refine ⟨139826487560077219214341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 186435316746769625619121 139826487560077219214341)
                  ·
                    refine ⟨26217466417514478602689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 139826487560077219214341 26217466417514478602689)
                    ·
                      rfl

theorem cell23_153175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 4, 2, 4].length) (baseStart_153175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153175 prefixEnd_153175 := by exact prefixLift 153175
  have htrace : WordTrace (prefixWord ++ tailWord_153175) baseStart_153175 baseEnd_153175 := by
    simpa [prefixWord, tailWord_153175, baseEnd_153175] using wordTrace_append hprefix tailTrace_153175
  have hstable : (prefixWord ++ tailWord_153175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153175).length < 2 ^ (prefixWord ++ tailWord_153175).sum := by decide
  have hdescent : baseEnd_153175 < baseStart_153175 := by decide
  rcases family_descends (prefixWord ++ tailWord_153175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153188 : List Nat := [2, 3, 1, 1, 2, 3, 3, 8]
def baseStart_153188 : Nat := 118140960795 + 153188 * 2 ^ 59
def prefixEnd_153188 : Nat := 4983230072969 + 3 ^ 40 * 153188 * 2
def baseEnd_153188 : Nat := 2913299055594514257241

theorem tailTrace_153188 : CollatzResearch.WordTrace tailWord_153188 prefixEnd_153188 2913299055594514257241 := by
  unfold tailWord_153188
  simp only [CollatzResearch.WordTrace]
  refine ⟨2793612684516756636306109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3724816912689008848408145 2793612684516756636306109)
  ·
    refine ⟨1047604756693783738614791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2793612684516756636306109 1047604756693783738614791)
    ·
      refine ⟨1571407135040675607922187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1047604756693783738614791 1571407135040675607922187)
      ·
        refine ⟨2357110702561013411883281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1571407135040675607922187 2357110702561013411883281)
        ·
          refine ⟨1767833026920760058912461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2357110702561013411883281 1767833026920760058912461)
          ·
            refine ⟨662937385095285022092173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1767833026920760058912461 662937385095285022092173)
            ·
              refine ⟨248601519410731883284565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 662937385095285022092173 248601519410731883284565)
              ·
                refine ⟨2913299055594514257241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 248601519410731883284565 2913299055594514257241)
                ·
                  rfl

theorem cell23_153188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 8].length) (baseStart_153188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153188 prefixEnd_153188 := by exact prefixLift 153188
  have htrace : WordTrace (prefixWord ++ tailWord_153188) baseStart_153188 baseEnd_153188 := by
    simpa [prefixWord, tailWord_153188, baseEnd_153188] using wordTrace_append hprefix tailTrace_153188
  have hstable : (prefixWord ++ tailWord_153188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153188).length < 2 ^ (prefixWord ++ tailWord_153188).sum := by decide
  have hdescent : baseEnd_153188 < baseStart_153188 := by decide
  rcases family_descends (prefixWord ++ tailWord_153188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153192 : List Nat := [2, 1, 4, 3, 1, 1, 2, 3, 2, 4]
def baseStart_153192 : Nat := 118140960795 + 153192 * 2 ^ 59
def prefixEnd_153192 : Nat := 4983230072969 + 3 ^ 40 * 153192 * 2
def baseEnd_153192 : Nat := 26220376141223289765163

theorem tailTrace_153192 : CollatzResearch.WordTrace tailWord_153192 prefixEnd_153192 26220376141223289765163 := by
  unfold tailWord_153192
  simp only [CollatzResearch.WordTrace]
  refine ⟨2793685630509510977878915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3724914174012681303838553 2793685630509510977878915)
  ·
    refine ⟨4190528445764266466818373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2793685630509510977878915 4190528445764266466818373)
    ·
      refine ⟨785724083580799962528445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4190528445764266466818373 785724083580799962528445)
      ·
        refine ⟨294646531342799985948167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 785724083580799962528445 294646531342799985948167)
        ·
          refine ⟨441969797014199978922251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294646531342799985948167 441969797014199978922251)
          ·
            refine ⟨662954695521299968383377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 441969797014199978922251 662954695521299968383377)
            ·
              refine ⟨497216021640974976287533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 662954695521299968383377 497216021640974976287533)
              ·
                refine ⟨186456008115365616107825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 497216021640974976287533 186456008115365616107825)
                ·
                  refine ⟨139842006086524212080869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 186456008115365616107825 139842006086524212080869)
                  ·
                    refine ⟨26220376141223289765163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 139842006086524212080869 26220376141223289765163)
                    ·
                      rfl

theorem cell23_153192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_153192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153192 prefixEnd_153192 := by exact prefixLift 153192
  have htrace : WordTrace (prefixWord ++ tailWord_153192) baseStart_153192 baseEnd_153192 := by
    simpa [prefixWord, tailWord_153192, baseEnd_153192] using wordTrace_append hprefix tailTrace_153192
  have hstable : (prefixWord ++ tailWord_153192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153192).length < 2 ^ (prefixWord ++ tailWord_153192).sum := by decide
  have hdescent : baseEnd_153192 < baseStart_153192 := by decide
  rcases family_descends (prefixWord ++ tailWord_153192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153256 : List Nat := [2, 1, 7, 1, 1, 2, 2, 7]
def baseStart_153256 : Nat := 118140960795 + 153256 * 2 ^ 59
def prefixEnd_153256 : Nat := 4983230072969 + 3 ^ 40 * 153256 * 2
def baseEnd_153256 : Nat := 2914592266131763662785

theorem tailTrace_153256 : CollatzResearch.WordTrace tailWord_153256 prefixEnd_153256 2914592266131763662785 := by
  unfold tailWord_153256
  simp only [CollatzResearch.WordTrace]
  refine ⟨2794852766393580443043811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3726470355191440590725081 2794852766393580443043811)
  ·
    refine ⟨4192279149590370664565717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2794852766393580443043811 4192279149590370664565717)
    ·
      refine ⟨98256542568524312450759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 4192279149590370664565717 98256542568524312450759)
      ·
        refine ⟨147384813852786468676139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98256542568524312450759 147384813852786468676139)
        ·
          refine ⟨221077220779179703014209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147384813852786468676139 221077220779179703014209)
          ·
            refine ⟨165807915584384777260657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221077220779179703014209 165807915584384777260657)
            ·
              refine ⟨124355936688288582945493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165807915584384777260657 124355936688288582945493)
              ·
                refine ⟨2914592266131763662785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 124355936688288582945493 2914592266131763662785)
                ·
                  rfl

theorem cell23_153256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 7].length) (baseStart_153256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153256 prefixEnd_153256 := by exact prefixLift 153256
  have htrace : WordTrace (prefixWord ++ tailWord_153256) baseStart_153256 baseEnd_153256 := by
    simpa [prefixWord, tailWord_153256, baseEnd_153256] using wordTrace_append hprefix tailTrace_153256
  have hstable : (prefixWord ++ tailWord_153256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153256).length < 2 ^ (prefixWord ++ tailWord_153256).sum := by decide
  have hdescent : baseEnd_153256 < baseStart_153256 := by decide
  rcases family_descends (prefixWord ++ tailWord_153256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153288 : List Nat := [2, 1, 3, 1, 2, 2, 1, 1, 1, 2, 7]
def baseStart_153288 : Nat := 118140960795 + 153288 * 2 ^ 59
def prefixEnd_153288 : Nat := 4983230072969 + 3 ^ 40 * 153288 * 2
def baseEnd_153288 : Nat := 78710422566501493695047

theorem tailTrace_153288 : CollatzResearch.WordTrace tailWord_153288 prefixEnd_153288 78710422566501493695047 := by
  unfold tailWord_153288
  simp only [CollatzResearch.WordTrace]
  refine ⟨2795436334335615175626259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3727248445780820234168345 2795436334335615175626259)
  ·
    refine ⟨4193154501503422763439389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2795436334335615175626259 4193154501503422763439389)
    ·
      refine ⟨1572432938063783536289771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4193154501503422763439389 1572432938063783536289771)
      ·
        refine ⟨2358649407095675304434657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1572432938063783536289771 2358649407095675304434657)
        ·
          refine ⟨1768987055321756478325993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2358649407095675304434657 1768987055321756478325993)
          ·
            refine ⟨1326740291491317358744495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1768987055321756478325993 1326740291491317358744495)
            ·
              refine ⟨1990110437236976038116743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1326740291491317358744495 1990110437236976038116743)
              ·
                refine ⟨2985165655855464057175115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1990110437236976038116743 2985165655855464057175115)
                ·
                  refine ⟨4477748483783196085762673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2985165655855464057175115 4477748483783196085762673)
                  ·
                    refine ⟨3358311362837397064322005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4477748483783196085762673 3358311362837397064322005)
                    ·
                      refine ⟨78710422566501493695047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 3358311362837397064322005 78710422566501493695047)
                      ·
                        rfl

theorem cell23_153288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_153288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153288 prefixEnd_153288 := by exact prefixLift 153288
  have htrace : WordTrace (prefixWord ++ tailWord_153288) baseStart_153288 baseEnd_153288 := by
    simpa [prefixWord, tailWord_153288, baseEnd_153288] using wordTrace_append hprefix tailTrace_153288
  have hstable : (prefixWord ++ tailWord_153288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153288).length < 2 ^ (prefixWord ++ tailWord_153288).sum := by decide
  have hdescent : baseEnd_153288 < baseStart_153288 := by decide
  rcases family_descends (prefixWord ++ tailWord_153288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153295 : List Nat := [1, 1, 2, 1, 1, 3, 1, 8, 5]
def baseStart_153295 : Nat := 118140960795 + 153295 * 2 ^ 59
def prefixEnd_153295 : Nat := 4983230072969 + 3 ^ 40 * 153295 * 2
def baseEnd_153295 : Nat := 8746001881231440700835

theorem tailTrace_153295 : CollatzResearch.WordTrace tailWord_153295 prefixEnd_153295 8746001881231440700835 := by
  unfold tailWord_153295
  simp only [CollatzResearch.WordTrace]
  refine ⟨5591127979645870546757339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3727418653097247031171559 5591127979645870546757339)
  ·
    refine ⟨8386691969468805820136009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5591127979645870546757339 8386691969468805820136009)
    ·
      refine ⟨6290018977101604365102007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8386691969468805820136009 6290018977101604365102007)
      ·
        refine ⟨9435028465652406547653011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6290018977101604365102007 9435028465652406547653011)
        ·
          refine ⟨14152542698478609821479517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9435028465652406547653011 14152542698478609821479517)
          ·
            refine ⟨5307203511929478683054819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14152542698478609821479517 5307203511929478683054819)
            ·
              refine ⟨7960805267894218024582229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5307203511929478683054819 7960805267894218024582229)
              ·
                refine ⟨93290686733135367475573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7960805267894218024582229 93290686733135367475573)
                ·
                  refine ⟨8746001881231440700835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 93290686733135367475573 8746001881231440700835)
                  ·
                    rfl

theorem cell23_153295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 8, 5].length) (baseStart_153295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153295 prefixEnd_153295 := by exact prefixLift 153295
  have htrace : WordTrace (prefixWord ++ tailWord_153295) baseStart_153295 baseEnd_153295 := by
    simpa [prefixWord, tailWord_153295, baseEnd_153295] using wordTrace_append hprefix tailTrace_153295
  have hstable : (prefixWord ++ tailWord_153295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153295).length < 2 ^ (prefixWord ++ tailWord_153295).sum := by decide
  have hdescent : baseEnd_153295 < baseStart_153295 := by decide
  rcases family_descends (prefixWord ++ tailWord_153295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153306 : List Nat := [3, 1, 1, 2, 2, 3, 4, 1, 2, 2, 2]
def baseStart_153306 : Nat := 118140960795 + 153306 * 2 ^ 59
def prefixEnd_153306 : Nat := 4983230072969 + 3 ^ 40 * 153306 * 2
def baseEnd_153306 : Nat := 78719665218282423269965

theorem tailTrace_153306 : CollatzResearch.WordTrace tailWord_153306 prefixEnd_153306 78719665218282423269965 := by
  unfold tailWord_153306
  simp only [CollatzResearch.WordTrace]
  refine ⟨1397882295651504856351943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3727686121737346283605181 1397882295651504856351943)
  ·
    refine ⟨2096823443477257284527915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1397882295651504856351943 2096823443477257284527915)
    ·
      refine ⟨3145235165215885926791873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2096823443477257284527915 3145235165215885926791873)
      ·
        refine ⟨2358926373911914445093905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3145235165215885926791873 2358926373911914445093905)
        ·
          refine ⟨1769194780433935833820429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2358926373911914445093905 1769194780433935833820429)
          ·
            refine ⟨663448042662725937682661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1769194780433935833820429 663448042662725937682661)
            ·
              refine ⟨124396507999261113315499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 663448042662725937682661 124396507999261113315499)
              ·
                refine ⟨186594761998891669973249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124396507999261113315499 186594761998891669973249)
                ·
                  refine ⟨139946071499168752479937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 186594761998891669973249 139946071499168752479937)
                  ·
                    refine ⟨104959553624376564359953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 139946071499168752479937 104959553624376564359953)
                    ·
                      refine ⟨78719665218282423269965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 104959553624376564359953 78719665218282423269965)
                      ·
                        rfl

theorem cell23_153306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 1, 2, 2, 2].length) (baseStart_153306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153306 prefixEnd_153306 := by exact prefixLift 153306
  have htrace : WordTrace (prefixWord ++ tailWord_153306) baseStart_153306 baseEnd_153306 := by
    simpa [prefixWord, tailWord_153306, baseEnd_153306] using wordTrace_append hprefix tailTrace_153306
  have hstable : (prefixWord ++ tailWord_153306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153306).length < 2 ^ (prefixWord ++ tailWord_153306).sum := by decide
  have hdescent : baseEnd_153306 < baseStart_153306 := by decide
  rcases family_descends (prefixWord ++ tailWord_153306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153372 : List Nat := [2, 2, 3, 1, 1, 2, 3, 2, 3, 4]
def baseStart_153372 : Nat := 118140960795 + 153372 * 2 ^ 59
def prefixEnd_153372 : Nat := 4983230072969 + 3 ^ 40 * 153372 * 2
def baseEnd_153372 : Nat := 26251184980493055014887

theorem tailTrace_153372 : CollatzResearch.WordTrace tailWord_153372 prefixEnd_153372 26251184980493055014887 := by
  unfold tailWord_153372
  simp only [CollatzResearch.WordTrace]
  refine ⟨2796968200183456348655185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3729290933577941798206913 2796968200183456348655185)
  ·
    refine ⟨2097726150137592261491389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2796968200183456348655185 2097726150137592261491389)
    ·
      refine ⟨786647306301597098059271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2097726150137592261491389 786647306301597098059271)
      ·
        refine ⟨1179970959452395647088907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 786647306301597098059271 1179970959452395647088907)
        ·
          refine ⟨1769956439178593470633361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1179970959452395647088907 1769956439178593470633361)
          ·
            refine ⟨1327467329383945102975021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1769956439178593470633361 1327467329383945102975021)
            ·
              refine ⟨497800248518979413615633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1327467329383945102975021 497800248518979413615633)
              ·
                refine ⟨373350186389234560211725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 497800248518979413615633 373350186389234560211725)
                ·
                  refine ⟨140006319895962960079397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 373350186389234560211725 140006319895962960079397)
                  ·
                    refine ⟨26251184980493055014887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 140006319895962960079397 26251184980493055014887)
                    ·
                      rfl

theorem cell23_153372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_153372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153372 prefixEnd_153372 := by exact prefixLift 153372
  have htrace : WordTrace (prefixWord ++ tailWord_153372) baseStart_153372 baseEnd_153372 := by
    simpa [prefixWord, tailWord_153372, baseEnd_153372] using wordTrace_append hprefix tailTrace_153372
  have hstable : (prefixWord ++ tailWord_153372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153372).length < 2 ^ (prefixWord ++ tailWord_153372).sum := by decide
  have hdescent : baseEnd_153372 < baseStart_153372 := by decide
  rcases family_descends (prefixWord ++ tailWord_153372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153402 : List Nat := [3, 1, 1, 1, 5, 1, 3, 2, 6]
def baseStart_153402 : Nat := 118140960795 + 153402 * 2 ^ 59
def prefixEnd_153402 : Nat := 4983230072969 + 3 ^ 40 * 153402 * 2
def baseEnd_153402 : Nat := 8752106595679338629947

theorem tailTrace_153402 : CollatzResearch.WordTrace tailWord_153402 prefixEnd_153402 8752106595679338629947 := by
  unfold tailWord_153402
  simp only [CollatzResearch.WordTrace]
  refine ⟨1398757647564556955225615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3730020393505485213934973 1398757647564556955225615)
  ·
    refine ⟨2098136471346835432838423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1398757647564556955225615 2098136471346835432838423)
    ·
      refine ⟨3147204707020253149257635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2098136471346835432838423 3147204707020253149257635)
      ·
        refine ⟨4720807060530379723886453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3147204707020253149257635 4720807060530379723886453)
        ·
          refine ⟨442575661924723099114355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4720807060530379723886453 442575661924723099114355)
          ·
            refine ⟨663863492887084648671533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 442575661924723099114355 663863492887084648671533)
            ·
              refine ⟨248948809832656743251825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 663863492887084648671533 248948809832656743251825)
              ·
                refine ⟨186711607374492557438869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 248948809832656743251825 186711607374492557438869)
                ·
                  refine ⟨8752106595679338629947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 186711607374492557438869 8752106595679338629947)
                  ·
                    rfl

theorem cell23_153402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 2, 6].length) (baseStart_153402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153402 prefixEnd_153402 := by exact prefixLift 153402
  have htrace : WordTrace (prefixWord ++ tailWord_153402) baseStart_153402 baseEnd_153402 := by
    simpa [prefixWord, tailWord_153402, baseEnd_153402] using wordTrace_append hprefix tailTrace_153402
  have hstable : (prefixWord ++ tailWord_153402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153402).length < 2 ^ (prefixWord ++ tailWord_153402).sum := by decide
  have hdescent : baseEnd_153402 < baseStart_153402 := by decide
  rcases family_descends (prefixWord ++ tailWord_153402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153406 : List Nat := [4, 2, 1, 2, 2, 1, 2, 4, 1, 4]
def baseStart_153406 : Nat := 118140960795 + 153406 * 2 ^ 59
def prefixEnd_153406 : Nat := 4983230072969 + 3 ^ 40 * 153406 * 2
def baseEnd_153406 : Nat := 26257004427910677339835

theorem tailTrace_153406 : CollatzResearch.WordTrace tailWord_153406 prefixEnd_153406 26257004427910677339835 := by
  unfold tailWord_153406
  simp only [CollatzResearch.WordTrace]
  refine ⟨699397060280467063006009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3730117654829157669365381 699397060280467063006009)
  ·
    refine ⟨524547795210350297254507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 699397060280467063006009 524547795210350297254507)
    ·
      refine ⟨786821692815525445881761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 524547795210350297254507 786821692815525445881761)
      ·
        refine ⟨590116269611644084411321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 786821692815525445881761 590116269611644084411321)
        ·
          refine ⟨442587202208733063308491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 590116269611644084411321 442587202208733063308491)
          ·
            refine ⟨663880803313099594962737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 442587202208733063308491 663880803313099594962737)
            ·
              refine ⟨497910602484824696222053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 663880803313099594962737 497910602484824696222053)
              ·
                refine ⟨93358237965904630541635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 497910602484824696222053 93358237965904630541635)
                ·
                  refine ⟨140037356948856945812453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93358237965904630541635 140037356948856945812453)
                  ·
                    refine ⟨26257004427910677339835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 140037356948856945812453 26257004427910677339835)
                    ·
                      rfl

theorem cell23_153406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_153406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153406 prefixEnd_153406 := by exact prefixLift 153406
  have htrace : WordTrace (prefixWord ++ tailWord_153406) baseStart_153406 baseEnd_153406 := by
    simpa [prefixWord, tailWord_153406, baseEnd_153406] using wordTrace_append hprefix tailTrace_153406
  have hstable : (prefixWord ++ tailWord_153406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153406).length < 2 ^ (prefixWord ++ tailWord_153406).sum := by decide
  have hdescent : baseEnd_153406 < baseStart_153406 := by decide
  rcases family_descends (prefixWord ++ tailWord_153406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153415 : List Nat := [1, 1, 4, 1, 2, 1, 2, 1, 5, 5]
def baseStart_153415 : Nat := 118140960795 + 153415 * 2 ^ 59
def prefixEnd_153415 : Nat := 4983230072969 + 3 ^ 40 * 153415 * 2
def baseEnd_153415 : Nat := 26258544869874165602321

theorem tailTrace_153415 : CollatzResearch.WordTrace tailWord_153415 prefixEnd_153415 26258544869874165602321 := by
  unfold tailWord_153415
  simp only [CollatzResearch.WordTrace]
  refine ⟨5595504739211131041125699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3730336492807420694083799 5595504739211131041125699)
  ·
    refine ⟨8393257108816696561688549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5595504739211131041125699 8393257108816696561688549)
    ·
      refine ⟨1573735707903130605316603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8393257108816696561688549 1573735707903130605316603)
      ·
        refine ⟨2360603561854695907974905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1573735707903130605316603 2360603561854695907974905)
        ·
          refine ⟨1770452671391021930981179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2360603561854695907974905 1770452671391021930981179)
          ·
            refine ⟨2655679007086532896471769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1770452671391021930981179 2655679007086532896471769)
            ·
              refine ⟨1991759255314899672353827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2655679007086532896471769 1991759255314899672353827)
              ·
                refine ⟨2987638882972349508530741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1991759255314899672353827 2987638882972349508530741)
                ·
                  refine ⟨280091145278657766424757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2987638882972349508530741 280091145278657766424757)
                  ·
                    refine ⟨26258544869874165602321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 280091145278657766424757 26258544869874165602321)
                    ·
                      rfl

theorem cell23_153415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 5, 5].length) (baseStart_153415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153415 prefixEnd_153415 := by exact prefixLift 153415
  have htrace : WordTrace (prefixWord ++ tailWord_153415) baseStart_153415 baseEnd_153415 := by
    simpa [prefixWord, tailWord_153415, baseEnd_153415] using wordTrace_append hprefix tailTrace_153415
  have hstable : (prefixWord ++ tailWord_153415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153415).length < 2 ^ (prefixWord ++ tailWord_153415).sum := by decide
  have hdescent : baseEnd_153415 < baseStart_153415 := by decide
  rcases family_descends (prefixWord ++ tailWord_153415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153429 : List Nat := [1, 3, 2, 2, 2, 2, 2, 2, 3, 1, 3]
def baseStart_153429 : Nat := 118140960795 + 153429 * 2 ^ 59
def prefixEnd_153429 : Nat := 4983230072969 + 3 ^ 40 * 153429 * 2
def baseEnd_153429 : Nat := 78782823338785442031899

theorem tailTrace_153429 : CollatzResearch.WordTrace tailWord_153429 prefixEnd_153429 78782823338785442031899 := by
  unfold tailWord_153429
  simp only [CollatzResearch.WordTrace]
  refine ⟨5596015361160411432135341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3730676907440274288090227 5596015361160411432135341)
  ·
    refine ⟨2098505760435154287050753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5596015361160411432135341 2098505760435154287050753)
    ·
      refine ⟨1573879320326365715288065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2098505760435154287050753 1573879320326365715288065)
      ·
        refine ⟨1180409490244774286466049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1573879320326365715288065 1180409490244774286466049)
        ·
          refine ⟨885307117683580714849537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1180409490244774286466049 885307117683580714849537)
          ·
            refine ⟨663980338262685536137153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 885307117683580714849537 663980338262685536137153)
            ·
              refine ⟨497985253697014152102865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 663980338262685536137153 497985253697014152102865)
              ·
                refine ⟨373488940272760614077149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 497985253697014152102865 373488940272760614077149)
                ·
                  refine ⟨140058352602285230278931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 373488940272760614077149 140058352602285230278931)
                  ·
                    refine ⟨210087528903427845418397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 140058352602285230278931 210087528903427845418397)
                    ·
                      refine ⟨78782823338785442031899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 210087528903427845418397 78782823338785442031899)
                      ·
                        rfl

theorem cell23_153429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_153429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153429 prefixEnd_153429 := by exact prefixLift 153429
  have htrace : WordTrace (prefixWord ++ tailWord_153429) baseStart_153429 baseEnd_153429 := by
    simpa [prefixWord, tailWord_153429, baseEnd_153429] using wordTrace_append hprefix tailTrace_153429
  have hstable : (prefixWord ++ tailWord_153429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153429).length < 2 ^ (prefixWord ++ tailWord_153429).sum := by decide
  have hdescent : baseEnd_153429 < baseStart_153429 := by decide
  rcases family_descends (prefixWord ++ tailWord_153429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153445 : List Nat := [1, 3, 1, 3, 1, 1, 1, 3, 3, 6]
def baseStart_153445 : Nat := 118140960795 + 153445 * 2 ^ 59
def prefixEnd_153445 : Nat := 4983230072969 + 3 ^ 40 * 153445 * 2
def baseEnd_153445 : Nat := 26263679676419126477275

theorem tailTrace_153445 : CollatzResearch.WordTrace tailWord_153445 prefixEnd_153445 26263679676419126477275 := by
  unfold tailWord_153445
  simp only [CollatzResearch.WordTrace]
  refine ⟨5596598929102446164717789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3731065952734964109811859 5596598929102446164717789)
  ·
    refine ⟨2098724598413417311769171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5596598929102446164717789 2098724598413417311769171)
    ·
      refine ⟨3148086897620125967653757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2098724598413417311769171 3148086897620125967653757)
      ·
        refine ⟨1180532586607547237870159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3148086897620125967653757 1180532586607547237870159)
        ·
          refine ⟨1770798879911320856805239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1180532586607547237870159 1770798879911320856805239)
          ·
            refine ⟨2656198319866981285207859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1770798879911320856805239 2656198319866981285207859)
            ·
              refine ⟨3984297479800471927811789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2656198319866981285207859 3984297479800471927811789)
              ·
                refine ⟨1494111554925176972929421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3984297479800471927811789 1494111554925176972929421)
                ·
                  refine ⟨560291833096941364848533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1494111554925176972929421 560291833096941364848533)
                  ·
                    refine ⟨26263679676419126477275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 560291833096941364848533 26263679676419126477275)
                    ·
                      rfl

theorem cell23_153445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 6].length) (baseStart_153445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153445 prefixEnd_153445 := by exact prefixLift 153445
  have htrace : WordTrace (prefixWord ++ tailWord_153445) baseStart_153445 baseEnd_153445 := by
    simpa [prefixWord, tailWord_153445, baseEnd_153445] using wordTrace_append hprefix tailTrace_153445
  have hstable : (prefixWord ++ tailWord_153445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153445).length < 2 ^ (prefixWord ++ tailWord_153445).sum := by decide
  have hdescent : baseEnd_153445 < baseStart_153445 := by decide
  rcases family_descends (prefixWord ++ tailWord_153445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153465 : List Nat := [1, 2, 1, 3, 2, 2, 1, 1, 3, 1, 6]
def baseStart_153465 : Nat := 118140960795 + 153465 * 2 ^ 59
def prefixEnd_153465 : Nat := 4983230072969 + 3 ^ 40 * 153465 * 2
def baseEnd_153465 : Nat := 78801308642347301181733

theorem tailTrace_153465 : CollatzResearch.WordTrace tailWord_153465 prefixEnd_153465 78801308642347301181733 := by
  unfold tailWord_153465
  simp only [CollatzResearch.WordTrace]
  refine ⟨5597328389029989580445849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3731552259353326386963899 5597328389029989580445849)
  ·
    refine ⟨4197996291772492185334387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5597328389029989580445849 4197996291772492185334387)
    ·
      refine ⟨6296994437658738278001581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4197996291772492185334387 6296994437658738278001581)
      ·
        refine ⟨2361372914122026854250593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6296994437658738278001581 2361372914122026854250593)
        ·
          refine ⟨1771029685591520140687945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2361372914122026854250593 1771029685591520140687945)
          ·
            refine ⟨1328272264193640105515959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1771029685591520140687945 1328272264193640105515959)
            ·
              refine ⟨1992408396290460158273939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1328272264193640105515959 1992408396290460158273939)
              ·
                refine ⟨2988612594435690237410909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1992408396290460158273939 2988612594435690237410909)
                ·
                  refine ⟨1120729722913383839029091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2988612594435690237410909 1120729722913383839029091)
                  ·
                    refine ⟨1681094584370075758543637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1120729722913383839029091 1681094584370075758543637)
                    ·
                      refine ⟨78801308642347301181733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1681094584370075758543637 78801308642347301181733)
                      ·
                        rfl

theorem cell23_153465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_153465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153465 prefixEnd_153465 := by exact prefixLift 153465
  have htrace : WordTrace (prefixWord ++ tailWord_153465) baseStart_153465 baseEnd_153465 := by
    simpa [prefixWord, tailWord_153465, baseEnd_153465] using wordTrace_append hprefix tailTrace_153465
  have hstable : (prefixWord ++ tailWord_153465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153465).length < 2 ^ (prefixWord ++ tailWord_153465).sum := by decide
  have hdescent : baseEnd_153465 < baseStart_153465 := by decide
  rcases family_descends (prefixWord ++ tailWord_153465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153472 : List Nat := [2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 3]
def baseStart_153472 : Nat := 118140960795 + 153472 * 2 ^ 59
def prefixEnd_153472 : Nat := 4983230072969 + 3 ^ 40 * 153472 * 2
def baseEnd_153472 : Nat := 78804903006928773794201

theorem tailTrace_153472 : CollatzResearch.WordTrace tailWord_153472 prefixEnd_153472 78804903006928773794201 := by
  unfold tailWord_153472
  simp only [CollatzResearch.WordTrace]
  refine ⟨2798791850002314887975335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3731722466669753183967113 2798791850002314887975335)
  ·
    refine ⟨4198187775003472331963003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2798791850002314887975335 4198187775003472331963003)
    ·
      refine ⟨6297281662505208497944505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4198187775003472331963003 6297281662505208497944505)
      ·
        refine ⟨4722961246878906373458379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6297281662505208497944505 4722961246878906373458379)
        ·
          refine ⟨7084441870318359560187569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4722961246878906373458379 7084441870318359560187569)
          ·
            refine ⟨5313331402738769670140677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7084441870318359560187569 5313331402738769670140677)
            ·
              refine ⟨996249638013519313151377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5313331402738769670140677 996249638013519313151377)
              ·
                refine ⟨747187228510139484863533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 996249638013519313151377 747187228510139484863533)
                ·
                  refine ⟨280195210691302306823825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 747187228510139484863533 280195210691302306823825)
                  ·
                    refine ⟨210146408018476730117869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 280195210691302306823825 210146408018476730117869)
                    ·
                      refine ⟨78804903006928773794201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 210146408018476730117869 78804903006928773794201)
                      ·
                        rfl

theorem cell23_153472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 3].length) (baseStart_153472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153472 prefixEnd_153472 := by exact prefixLift 153472
  have htrace : WordTrace (prefixWord ++ tailWord_153472) baseStart_153472 baseEnd_153472 := by
    simpa [prefixWord, tailWord_153472, baseEnd_153472] using wordTrace_append hprefix tailTrace_153472
  have hstable : (prefixWord ++ tailWord_153472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153472).length < 2 ^ (prefixWord ++ tailWord_153472).sum := by decide
  have hdescent : baseEnd_153472 < baseStart_153472 := by decide
  rcases family_descends (prefixWord ++ tailWord_153472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153475 : List Nat := [1, 1, 1, 3, 4, 2, 1, 10]
def baseStart_153475 : Nat := 118140960795 + 153475 * 2 ^ 59
def prefixEnd_153475 : Nat := 4983230072969 + 3 ^ 40 * 153475 * 2
def baseEnd_153475 : Nat := 2918757164773787483581

theorem tailTrace_153475 : CollatzResearch.WordTrace tailWord_153475 prefixEnd_153475 2918757164773787483581 := by
  unfold tailWord_153475
  simp only [CollatzResearch.WordTrace]
  refine ⟨5597693118993761288309879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3731795412662507525539919 5597693118993761288309879)
  ·
    refine ⟨8396539678490641932464819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5597693118993761288309879 8396539678490641932464819)
    ·
      refine ⟨12594809517735962898697229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8396539678490641932464819 12594809517735962898697229)
      ·
        refine ⟨4723053569150986087011461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12594809517735962898697229 4723053569150986087011461)
        ·
          refine ⟨885572544215809891314649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4723053569150986087011461 885572544215809891314649)
          ·
            refine ⟨664179408161857418485987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 885572544215809891314649 664179408161857418485987)
            ·
              refine ⟨996269112242786127728981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 664179408161857418485987 996269112242786127728981)
              ·
                refine ⟨2918757164773787483581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 996269112242786127728981 2918757164773787483581)
                ·
                  rfl

theorem cell23_153475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 10].length) (baseStart_153475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153475 prefixEnd_153475 := by exact prefixLift 153475
  have htrace : WordTrace (prefixWord ++ tailWord_153475) baseStart_153475 baseEnd_153475 := by
    simpa [prefixWord, tailWord_153475, baseEnd_153475] using wordTrace_append hprefix tailTrace_153475
  have hstable : (prefixWord ++ tailWord_153475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153475).length < 2 ^ (prefixWord ++ tailWord_153475).sum := by decide
  have hdescent : baseEnd_153475 < baseStart_153475 := by decide
  rcases family_descends (prefixWord ++ tailWord_153475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153486 : List Nat := [4, 1, 1, 5, 1, 1, 1, 1, 3, 1, 4]
def baseStart_153486 : Nat := 118140960795 + 153486 * 2 ^ 59
def prefixEnd_153486 : Nat := 4983230072969 + 3 ^ 40 * 153486 * 2
def baseEnd_153486 : Nat := 78812091736091719019137

theorem tailTrace_153486 : CollatzResearch.WordTrace tailWord_153486 prefixEnd_153486 78812091736091719019137 := by
  unfold tailWord_153486
  simp only [CollatzResearch.WordTrace]
  refine ⟨699761790244238770870039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3732062881302606777973541 699761790244238770870039)
  ·
    refine ⟨1049642685366358156305059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 699761790244238770870039 1049642685366358156305059)
    ·
      refine ⟨1574464028049537234457589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1049642685366358156305059 1574464028049537234457589)
      ·
        refine ⟨147606002629644115730399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1574464028049537234457589 147606002629644115730399)
        ·
          refine ⟨221409003944466173595599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147606002629644115730399 221409003944466173595599)
          ·
            refine ⟨332113505916699260393399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221409003944466173595599 332113505916699260393399)
            ·
              refine ⟨498170258875048890590099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 332113505916699260393399 498170258875048890590099)
              ·
                refine ⟨747255388312573335885149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 498170258875048890590099 747255388312573335885149)
                ·
                  refine ⟨280220770617215000956931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 747255388312573335885149 280220770617215000956931)
                  ·
                    refine ⟨420331155925822501435397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 280220770617215000956931 420331155925822501435397)
                    ·
                      refine ⟨78812091736091719019137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 420331155925822501435397 78812091736091719019137)
                      ·
                        rfl

theorem cell23_153486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_153486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153486 prefixEnd_153486 := by exact prefixLift 153486
  have htrace : WordTrace (prefixWord ++ tailWord_153486) baseStart_153486 baseEnd_153486 := by
    simpa [prefixWord, tailWord_153486, baseEnd_153486] using wordTrace_append hprefix tailTrace_153486
  have hstable : (prefixWord ++ tailWord_153486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153486).length < 2 ^ (prefixWord ++ tailWord_153486).sum := by decide
  have hdescent : baseEnd_153486 < baseStart_153486 := by decide
  rcases family_descends (prefixWord ++ tailWord_153486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153489 : List Nat := [1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 3]
def baseStart_153489 : Nat := 118140960795 + 153489 * 2 ^ 59
def prefixEnd_153489 : Nat := 4983230072969 + 3 ^ 40 * 153489 * 2
def baseEnd_153489 : Nat := 78813632178055207281623

theorem tailTrace_153489 : CollatzResearch.WordTrace tailWord_153489 prefixEnd_153489 78813632178055207281623 := by
  unfold tailWord_153489
  simp only [CollatzResearch.WordTrace]
  refine ⟨5598203740943041679319521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3732135827295361119546347 5598203740943041679319521)
  ·
    refine ⟨4198652805707281259489641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5598203740943041679319521 4198652805707281259489641)
    ·
      refine ⟨3148989604280460944617231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4198652805707281259489641 3148989604280460944617231)
      ·
        refine ⟨4723484406420691416925847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3148989604280460944617231 4723484406420691416925847)
        ·
          refine ⟨7085226609631037125388771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4723484406420691416925847 7085226609631037125388771)
          ·
            refine ⟨10627839914446555688083157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7085226609631037125388771 10627839914446555688083157)
            ·
              refine ⟨249089997994841148939449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 10627839914446555688083157 249089997994841148939449)
              ·
                refine ⟨186817498496130861704587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 249089997994841148939449 186817498496130861704587)
                ·
                  refine ⟨280226247744196292556881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 186817498496130861704587 280226247744196292556881)
                  ·
                    refine ⟨210169685808147219417661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 280226247744196292556881 210169685808147219417661)
                    ·
                      refine ⟨78813632178055207281623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 210169685808147219417661 78813632178055207281623)
                      ·
                        rfl

theorem cell23_153489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 3].length) (baseStart_153489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153489 prefixEnd_153489 := by exact prefixLift 153489
  have htrace : WordTrace (prefixWord ++ tailWord_153489) baseStart_153489 baseEnd_153489 := by
    simpa [prefixWord, tailWord_153489, baseEnd_153489] using wordTrace_append hprefix tailTrace_153489
  have hstable : (prefixWord ++ tailWord_153489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153489).length < 2 ^ (prefixWord ++ tailWord_153489).sum := by decide
  have hdescent : baseEnd_153489 < baseStart_153489 := by decide
  rcases family_descends (prefixWord ++ tailWord_153489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153492 : List Nat := [2, 4, 2, 1, 1, 2, 2, 9]
def baseStart_153492 : Nat := 118140960795 + 153492 * 2 ^ 59
def prefixEnd_153492 : Nat := 4983230072969 + 3 ^ 40 * 153492 * 2
def baseEnd_153492 : Nat := 2919080467408099834967

theorem tailTrace_153492 : CollatzResearch.WordTrace tailWord_153492 prefixEnd_153492 2919080467408099834967 := by
  unfold tailWord_153492
  simp only [CollatzResearch.WordTrace]
  refine ⟨2799156579966086595839365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3732208773288115461119153 2799156579966086595839365)
  ·
    refine ⟨524841858743641236719881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2799156579966086595839365 524841858743641236719881)
    ·
      refine ⟨393631394057730927539911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 524841858743641236719881 393631394057730927539911)
      ·
        refine ⟨590447091086596391309867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 393631394057730927539911 590447091086596391309867)
        ·
          refine ⟨885670636629894586964801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 590447091086596391309867 885670636629894586964801)
          ·
            refine ⟨664252977472420940223601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 885670636629894586964801 664252977472420940223601)
            ·
              refine ⟨498189733104315705167701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 664252977472420940223601 498189733104315705167701)
              ·
                refine ⟨2919080467408099834967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 498189733104315705167701 2919080467408099834967)
                ·
                  rfl

theorem cell23_153492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 9].length) (baseStart_153492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153492 prefixEnd_153492 := by exact prefixLift 153492
  have htrace : WordTrace (prefixWord ++ tailWord_153492) baseStart_153492 baseEnd_153492 := by
    simpa [prefixWord, tailWord_153492, baseEnd_153492] using wordTrace_append hprefix tailTrace_153492
  have hstable : (prefixWord ++ tailWord_153492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153492).length < 2 ^ (prefixWord ++ tailWord_153492).sum := by decide
  have hdescent : baseEnd_153492 < baseStart_153492 := by decide
  rcases family_descends (prefixWord ++ tailWord_153492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153506 : List Nat := [3, 3, 1, 2, 3, 2, 1, 1, 1, 1, 5]
def baseStart_153506 : Nat := 118140960795 + 153506 * 2 ^ 59
def prefixEnd_153506 : Nat := 4983230072969 + 3 ^ 40 * 153506 * 2
def baseEnd_153506 : Nat := 78822361349181640769045

theorem tailTrace_153506 : CollatzResearch.WordTrace tailWord_153506 prefixEnd_153506 78822361349181640769045 := by
  unfold tailWord_153506
  simp only [CollatzResearch.WordTrace]
  refine ⟨1399705945470363395672093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3732549187920969055125581 1399705945470363395672093)
  ·
    refine ⟨524889729551386273377035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1399705945470363395672093 524889729551386273377035)
    ·
      refine ⟨787334594327079410065553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 524889729551386273377035 787334594327079410065553)
      ·
        refine ⟨590500945745309557549165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 787334594327079410065553 590500945745309557549165)
        ·
          refine ⟨221437854654491084080937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 590500945745309557549165 221437854654491084080937)
          ·
            refine ⟨166078390990868313060703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221437854654491084080937 166078390990868313060703)
            ·
              refine ⟨249117586486302469591055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166078390990868313060703 249117586486302469591055)
              ·
                refine ⟨373676379729453704386583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 249117586486302469591055 373676379729453704386583)
                ·
                  refine ⟨560514569594180556579875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 373676379729453704386583 560514569594180556579875)
                  ·
                    refine ⟨840771854391270834869813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 560514569594180556579875 840771854391270834869813)
                    ·
                      refine ⟨78822361349181640769045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 840771854391270834869813 78822361349181640769045)
                      ·
                        rfl

theorem cell23_153506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_153506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153506 prefixEnd_153506 := by exact prefixLift 153506
  have htrace : WordTrace (prefixWord ++ tailWord_153506) baseStart_153506 baseEnd_153506 := by
    simpa [prefixWord, tailWord_153506, baseEnd_153506] using wordTrace_append hprefix tailTrace_153506
  have hstable : (prefixWord ++ tailWord_153506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153506).length < 2 ^ (prefixWord ++ tailWord_153506).sum := by decide
  have hdescent : baseEnd_153506 < baseStart_153506 := by decide
  rcases family_descends (prefixWord ++ tailWord_153506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153529 : List Nat := [1, 2, 1, 4, 2, 1, 1, 1, 5, 3, 2]
def baseStart_153529 : Nat := 118140960795 + 153529 * 2 ^ 59
def prefixEnd_153529 : Nat := 4983230072969 + 3 ^ 40 * 153529 * 2
def baseEnd_153529 : Nat := 78834171404235050781439

theorem tailTrace_153529 : CollatzResearch.WordTrace tailWord_153529 prefixEnd_153529 78834171404235050781439 := by
  unfold tailWord_153529
  simp only [CollatzResearch.WordTrace]
  refine ⟨5599662660798128510775641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3733108440532085673850427 5599662660798128510775641)
  ·
    refine ⟨4199746995598596383081731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5599662660798128510775641 4199746995598596383081731)
    ·
      refine ⟨6299620493397894574622597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4199746995598596383081731 6299620493397894574622597)
      ·
        refine ⟨1181178842512105232741737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6299620493397894574622597 1181178842512105232741737)
        ·
          refine ⟨885884131884078924556303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1181178842512105232741737 885884131884078924556303)
          ·
            refine ⟨1328826197826118386834455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 885884131884078924556303 1328826197826118386834455)
            ·
              refine ⟨1993239296739177580251683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1328826197826118386834455 1993239296739177580251683)
              ·
                refine ⟨2989858945108766370377525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1993239296739177580251683 2989858945108766370377525)
                ·
                  refine ⟨280299276103946847222893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2989858945108766370377525 280299276103946847222893)
                  ·
                    refine ⟨105112228538980067708585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 280299276103946847222893 105112228538980067708585)
                    ·
                      refine ⟨78834171404235050781439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 105112228538980067708585 78834171404235050781439)
                      ·
                        rfl

theorem cell23_153529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 5, 3, 2].length) (baseStart_153529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153529 prefixEnd_153529 := by exact prefixLift 153529
  have htrace : WordTrace (prefixWord ++ tailWord_153529) baseStart_153529 baseEnd_153529 := by
    simpa [prefixWord, tailWord_153529, baseEnd_153529] using wordTrace_append hprefix tailTrace_153529
  have hstable : (prefixWord ++ tailWord_153529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153529).length < 2 ^ (prefixWord ++ tailWord_153529).sum := by decide
  have hdescent : baseEnd_153529 < baseStart_153529 := by decide
  rcases family_descends (prefixWord ++ tailWord_153529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153559 : List Nat := [1, 1, 3, 2, 1, 1, 3, 4, 1, 4, 2]
def baseStart_153559 : Nat := 118140960795 + 153559 * 2 ^ 59
def prefixEnd_153559 : Nat := 4983230072969 + 3 ^ 40 * 153559 * 2
def baseEnd_153559 : Nat := 78849575823869933406301

theorem tailTrace_153559 : CollatzResearch.WordTrace tailWord_153559 prefixEnd_153559 78849575823869933406301 := by
  unfold tailWord_153559
  simp only [CollatzResearch.WordTrace]
  refine ⟨5600756850689443634367731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3733837900459629089578487 5600756850689443634367731)
  ·
    refine ⟨8401135276034165451551597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5600756850689443634367731 8401135276034165451551597)
    ·
      refine ⟨3150425728512812044331849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8401135276034165451551597 3150425728512812044331849)
      ·
        refine ⟨2362819296384609033248887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3150425728512812044331849 2362819296384609033248887)
        ·
          refine ⟨3544228944576913549873331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2362819296384609033248887 3544228944576913549873331)
          ·
            refine ⟨5316343416865370324809997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3544228944576913549873331 5316343416865370324809997)
            ·
              refine ⟨1993628781324513871803749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5316343416865370324809997 1993628781324513871803749)
              ·
                refine ⟨373805396498346350963203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1993628781324513871803749 373805396498346350963203)
                ·
                  refine ⟨560708094747519526444805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 373805396498346350963203 560708094747519526444805)
                  ·
                    refine ⟨105132767765159911208401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 560708094747519526444805 105132767765159911208401)
                    ·
                      refine ⟨78849575823869933406301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 105132767765159911208401 78849575823869933406301)
                      ·
                        rfl

theorem cell23_153559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 4, 2].length) (baseStart_153559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153559 prefixEnd_153559 := by exact prefixLift 153559
  have htrace : WordTrace (prefixWord ++ tailWord_153559) baseStart_153559 baseEnd_153559 := by
    simpa [prefixWord, tailWord_153559, baseEnd_153559] using wordTrace_append hprefix tailTrace_153559
  have hstable : (prefixWord ++ tailWord_153559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153559).length < 2 ^ (prefixWord ++ tailWord_153559).sum := by decide
  have hdescent : baseEnd_153559 < baseStart_153559 := by decide
  rcases family_descends (prefixWord ++ tailWord_153559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153572 : List Nat := [2, 3, 1, 1, 1, 1, 3, 1, 4, 2, 4]
def baseStart_153572 : Nat := 118140960795 + 153572 * 2 ^ 59
def prefixEnd_153572 : Nat := 4983230072969 + 3 ^ 40 * 153572 * 2
def baseEnd_153572 : Nat := 78856251072378382543741

theorem tailTrace_153572 : CollatzResearch.WordTrace tailWord_153572 prefixEnd_153572 78856251072378382543741 := by
  unfold tailWord_153572
  simp only [CollatzResearch.WordTrace]
  refine ⟨2800615499821173427295485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3734153999761564569727313 2800615499821173427295485)
  ·
    refine ⟨1050230812432940035235807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2800615499821173427295485 1050230812432940035235807)
    ·
      refine ⟨1575346218649410052853711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1050230812432940035235807 1575346218649410052853711)
      ·
        refine ⟨2363019327974115079280567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1575346218649410052853711 2363019327974115079280567)
        ·
          refine ⟨3544528991961172618920851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2363019327974115079280567 3544528991961172618920851)
          ·
            refine ⟨5316793487941758928381277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3544528991961172618920851 5316793487941758928381277)
            ·
              refine ⟨1993797557978159598142979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5316793487941758928381277 1993797557978159598142979)
              ·
                refine ⟨2990696336967239397214469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1993797557978159598142979 2990696336967239397214469)
                ·
                  refine ⟨560755563181357386977713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2990696336967239397214469 560755563181357386977713)
                  ·
                    refine ⟨420566672386018040233285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 560755563181357386977713 420566672386018040233285)
                    ·
                      refine ⟨78856251072378382543741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 420566672386018040233285 78856251072378382543741)
                      ·
                        rfl

theorem cell23_153572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_153572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153572 prefixEnd_153572 := by exact prefixLift 153572
  have htrace : WordTrace (prefixWord ++ tailWord_153572) baseStart_153572 baseEnd_153572 := by
    simpa [prefixWord, tailWord_153572, baseEnd_153572] using wordTrace_append hprefix tailTrace_153572
  have hstable : (prefixWord ++ tailWord_153572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153572).length < 2 ^ (prefixWord ++ tailWord_153572).sum := by decide
  have hdescent : baseEnd_153572 < baseStart_153572 := by decide
  rcases family_descends (prefixWord ++ tailWord_153572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153612 : List Nat := [2, 2, 1, 2, 3, 1, 1, 3, 1, 7]
def baseStart_153612 : Nat := 118140960795 + 153612 * 2 ^ 59
def prefixEnd_153612 : Nat := 4983230072969 + 3 ^ 40 * 153612 * 2
def baseEnd_153612 : Nat := 26292263432852742014519

theorem tailTrace_153612 : CollatzResearch.WordTrace tailWord_153612 prefixEnd_153612 26292263432852742014519 := by
  unfold tailWord_153612
  simp only [CollatzResearch.WordTrace]
  refine ⟨2801344959748716843023545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3735126612998289124031393 2801344959748716843023545)
  ·
    refine ⟨2101008719811537632267659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2801344959748716843023545 2101008719811537632267659)
    ·
      refine ⟨3151513079717306448401489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2101008719811537632267659 3151513079717306448401489)
      ·
        refine ⟨2363634809787979836301117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3151513079717306448401489 2363634809787979836301117)
        ·
          refine ⟨886363053670492438612919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2363634809787979836301117 886363053670492438612919)
          ·
            refine ⟨1329544580505738657919379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 886363053670492438612919 1329544580505738657919379)
            ·
              refine ⟨1994316870758607986879069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1329544580505738657919379 1994316870758607986879069)
              ·
                refine ⟨747868826534477995079651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1994316870758607986879069 747868826534477995079651)
                ·
                  refine ⟨1121803239801716992619477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 747868826534477995079651 1121803239801716992619477)
                  ·
                    refine ⟨26292263432852742014519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1121803239801716992619477 26292263432852742014519)
                    ·
                      rfl

theorem cell23_153612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 1, 7].length) (baseStart_153612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153612 prefixEnd_153612 := by exact prefixLift 153612
  have htrace : WordTrace (prefixWord ++ tailWord_153612) baseStart_153612 baseEnd_153612 := by
    simpa [prefixWord, tailWord_153612, baseEnd_153612] using wordTrace_append hprefix tailTrace_153612
  have hstable : (prefixWord ++ tailWord_153612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153612).length < 2 ^ (prefixWord ++ tailWord_153612).sum := by decide
  have hdescent : baseEnd_153612 < baseStart_153612 := by decide
  rcases family_descends (prefixWord ++ tailWord_153612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153629 : List Nat := [1, 4, 2, 2, 2, 1, 1, 1, 4, 5]
def baseStart_153629 : Nat := 118140960795 + 153629 * 2 ^ 59
def prefixEnd_153629 : Nat := 4983230072969 + 3 ^ 40 * 153629 * 2
def baseEnd_153629 : Nat := 26295173156561553176993

theorem tailTrace_153629 : CollatzResearch.WordTrace tailWord_153629 prefixEnd_153629 26295173156561553176993 := by
  unfold tailWord_153629
  simp only [CollatzResearch.WordTrace]
  refine ⟨5603309960435845589415941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3735539973623897059610627 5603309960435845589415941)
  ·
    refine ⟨1050620617581721048015489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5603309960435845589415941 1050620617581721048015489)
    ·
      refine ⟨787965463186290786011617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1050620617581721048015489 787965463186290786011617)
      ·
        refine ⟨590974097389718089508713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 787965463186290786011617 590974097389718089508713)
        ·
          refine ⟨443230573042288567131535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 590974097389718089508713 443230573042288567131535)
          ·
            refine ⟨664845859563432850697303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 443230573042288567131535 664845859563432850697303)
            ·
              refine ⟨997268789345149276045955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 664845859563432850697303 997268789345149276045955)
              ·
                refine ⟨1495903184017723914068933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 997268789345149276045955 1495903184017723914068933)
                ·
                  refine ⟨280481847003323233887925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1495903184017723914068933 280481847003323233887925)
                  ·
                    refine ⟨26295173156561553176993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 280481847003323233887925 26295173156561553176993)
                    ·
                      rfl

theorem cell23_153629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_153629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153629 prefixEnd_153629 := by exact prefixLift 153629
  have htrace : WordTrace (prefixWord ++ tailWord_153629) baseStart_153629 baseEnd_153629 := by
    simpa [prefixWord, tailWord_153629, baseEnd_153629] using wordTrace_append hprefix tailTrace_153629
  have hstable : (prefixWord ++ tailWord_153629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153629).length < 2 ^ (prefixWord ++ tailWord_153629).sum := by decide
  have hdescent : baseEnd_153629 < baseStart_153629 := by decide
  rcases family_descends (prefixWord ++ tailWord_153629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153633 : List Nat := [1, 2, 3, 2, 4, 1, 3, 2, 5]
def baseStart_153633 : Nat := 118140960795 + 153633 * 2 ^ 59
def prefixEnd_153633 : Nat := 4983230072969 + 3 ^ 40 * 153633 * 2
def baseEnd_153633 : Nat := 8765285932478071542329

theorem tailTrace_153633 : CollatzResearch.WordTrace tailWord_153633 prefixEnd_153633 8765285932478071542329 := by
  unfold tailWord_153633
  simp only [CollatzResearch.WordTrace]
  refine ⟨5603455852421354272561553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3735637234947569515041035 5603455852421354272561553)
  ·
    refine ⟨4202591889316015704421165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5603455852421354272561553 4202591889316015704421165)
    ·
      refine ⟨1575971958493505889157937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4202591889316015704421165 1575971958493505889157937)
      ·
        refine ⟨1181978968870129416868453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1575971958493505889157937 1181978968870129416868453)
        ·
          refine ⟨221621056663149265662835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1181978968870129416868453 221621056663149265662835)
          ·
            refine ⟨332431584994723898494253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221621056663149265662835 332431584994723898494253)
            ·
              refine ⟨124661844373021461935345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 332431584994723898494253 124661844373021461935345)
              ·
                refine ⟨93496383279766096451509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124661844373021461935345 93496383279766096451509)
                ·
                  refine ⟨8765285932478071542329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 93496383279766096451509 8765285932478071542329)
                  ·
                    rfl

theorem cell23_153633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 2, 5].length) (baseStart_153633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153633 prefixEnd_153633 := by exact prefixLift 153633
  have htrace : WordTrace (prefixWord ++ tailWord_153633) baseStart_153633 baseEnd_153633 := by
    simpa [prefixWord, tailWord_153633, baseEnd_153633] using wordTrace_append hprefix tailTrace_153633
  have hstable : (prefixWord ++ tailWord_153633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153633).length < 2 ^ (prefixWord ++ tailWord_153633).sum := by decide
  have hdescent : baseEnd_153633 < baseStart_153633 := by decide
  rcases family_descends (prefixWord ++ tailWord_153633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153672 : List Nat := [2, 1, 3, 1, 1, 1, 2, 4, 8]
def baseStart_153672 : Nat := 118140960795 + 153672 * 2 ^ 59
def prefixEnd_153672 : Nat := 4983230072969 + 3 ^ 40 * 153672 * 2
def baseEnd_153672 : Nat := 8767511015314221254809

theorem tailTrace_153672 : CollatzResearch.WordTrace tailWord_153672 prefixEnd_153672 8767511015314221254809 := by
  unfold tailWord_153672
  simp only [CollatzResearch.WordTrace]
  refine ⟨2802439149640031966615635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3736585532853375955487513 2802439149640031966615635)
  ·
    refine ⟨4203658724460047949923453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2802439149640031966615635 4203658724460047949923453)
    ·
      refine ⟨1576372021672517981221295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4203658724460047949923453 1576372021672517981221295)
      ·
        refine ⟨2364558032508776971831943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1576372021672517981221295 2364558032508776971831943)
        ·
          refine ⟨3546837048763165457747915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2364558032508776971831943 3546837048763165457747915)
          ·
            refine ⟨5320255573144748186621873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3546837048763165457747915 5320255573144748186621873)
            ·
              refine ⟨3990191679858561139966405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5320255573144748186621873 3990191679858561139966405)
              ·
                refine ⟨748160939973480213743701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3990191679858561139966405 748160939973480213743701)
                ·
                  refine ⟨8767511015314221254809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 748160939973480213743701 8767511015314221254809)
                  ·
                    rfl

theorem cell23_153672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 8].length) (baseStart_153672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153672 prefixEnd_153672 := by exact prefixLift 153672
  have htrace : WordTrace (prefixWord ++ tailWord_153672) baseStart_153672 baseEnd_153672 := by
    simpa [prefixWord, tailWord_153672, baseEnd_153672] using wordTrace_append hprefix tailTrace_153672
  have hstable : (prefixWord ++ tailWord_153672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153672).length < 2 ^ (prefixWord ++ tailWord_153672).sum := by decide
  have hdescent : baseEnd_153672 < baseStart_153672 := by decide
  rcases family_descends (prefixWord ++ tailWord_153672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153689 : List Nat := [1, 2, 1, 2, 2, 1, 6, 2, 6]
def baseStart_153689 : Nat := 118140960795 + 153689 * 2 ^ 59
def prefixEnd_153689 : Nat := 4983230072969 + 3 ^ 40 * 153689 * 2
def baseEnd_153689 : Nat := 8768480923217158308967

theorem tailTrace_153689 : CollatzResearch.WordTrace tailWord_153689 prefixEnd_153689 8768480923217158308967 := by
  unfold tailWord_153689
  simp only [CollatzResearch.WordTrace]
  refine ⟨5605498340218475836600121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3736998893478983891066747 5605498340218475836600121)
  ·
    refine ⟨4204123755163856877450091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5605498340218475836600121 4204123755163856877450091)
    ·
      refine ⟨6306185632745785316175137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4204123755163856877450091 6306185632745785316175137)
      ·
        refine ⟨4729639224559338987131353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6306185632745785316175137 4729639224559338987131353)
        ·
          refine ⟨3547229418419504240348515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4729639224559338987131353 3547229418419504240348515)
          ·
            refine ⟨5320844127629256360522773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3547229418419504240348515 5320844127629256360522773)
            ·
              refine ⟨249414568482621391899505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5320844127629256360522773 249414568482621391899505)
              ·
                refine ⟨187060926361966043924629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 249414568482621391899505 187060926361966043924629)
                ·
                  refine ⟨8768480923217158308967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 187060926361966043924629 8768480923217158308967)
                  ·
                    rfl

theorem cell23_153689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 2, 6].length) (baseStart_153689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153689 prefixEnd_153689 := by exact prefixLift 153689
  have htrace : WordTrace (prefixWord ++ tailWord_153689) baseStart_153689 baseEnd_153689 := by
    simpa [prefixWord, tailWord_153689, baseEnd_153689] using wordTrace_append hprefix tailTrace_153689
  have hstable : (prefixWord ++ tailWord_153689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153689).length < 2 ^ (prefixWord ++ tailWord_153689).sum := by decide
  have hdescent : baseEnd_153689 < baseStart_153689 := by decide
  rcases family_descends (prefixWord ++ tailWord_153689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153719 : List Nat := [1, 1, 3, 1, 1, 5, 2, 1, 3, 5]
def baseStart_153719 : Nat := 118140960795 + 153719 * 2 ^ 59
def prefixEnd_153719 : Nat := 4983230072969 + 3 ^ 40 * 153719 * 2
def baseEnd_153719 : Nat := 26310577576196435801855

theorem tailTrace_153719 : CollatzResearch.WordTrace tailWord_153719 prefixEnd_153719 26310577576196435801855 := by
  unfold tailWord_153719
  simp only [CollatzResearch.WordTrace]
  refine ⟨5606592530109790960192211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3737728353406527306794807 5606592530109790960192211)
  ·
    refine ⟨8409888795164686440288317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5606592530109790960192211 8409888795164686440288317)
    ·
      refine ⟨3153708298186757415108119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8409888795164686440288317 3153708298186757415108119)
      ·
        refine ⟨4730562447280136122662179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3153708298186757415108119 4730562447280136122662179)
        ·
          refine ⟨7095843670920204183993269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4730562447280136122662179 7095843670920204183993269)
          ·
            refine ⟨665235344148769142249369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7095843670920204183993269 665235344148769142249369)
            ·
              refine ⟨498926508111576856687027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 665235344148769142249369 498926508111576856687027)
              ·
                refine ⟨748389762167365285030541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 498926508111576856687027 748389762167365285030541)
                ·
                  refine ⟨280646160812761981886453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 748389762167365285030541 280646160812761981886453)
                  ·
                    refine ⟨26310577576196435801855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 280646160812761981886453 26310577576196435801855)
                    ·
                      rfl

theorem cell23_153719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 3, 5].length) (baseStart_153719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153719 prefixEnd_153719 := by exact prefixLift 153719
  have htrace : WordTrace (prefixWord ++ tailWord_153719) baseStart_153719 baseEnd_153719 := by
    simpa [prefixWord, tailWord_153719, baseEnd_153719] using wordTrace_append hprefix tailTrace_153719
  have hstable : (prefixWord ++ tailWord_153719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153719).length < 2 ^ (prefixWord ++ tailWord_153719).sum := by decide
  have hdescent : baseEnd_153719 < baseStart_153719 := by decide
  rcases family_descends (prefixWord ++ tailWord_153719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153770 : List Nat := [3, 1, 5, 1, 2, 1, 2, 2, 1, 5]
def baseStart_153770 : Nat := 118140960795 + 153770 * 2 ^ 59
def prefixEnd_153770 : Nat := 4983230072969 + 3 ^ 40 * 153770 * 2
def baseEnd_153770 : Nat := 26319306747322869289277

theorem tailTrace_153770 : CollatzResearch.WordTrace tailWord_153770 prefixEnd_153770 26319306747322869289277 := by
  unfold tailWord_153770
  simp only [CollatzResearch.WordTrace]
  refine ⟨1402113163231256667574691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3738968435283351113532509 1402113163231256667574691)
  ·
    refine ⟨2103169744846885001362037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1402113163231256667574691 2103169744846885001362037)
    ·
      refine ⟨197172163579395468877691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2103169744846885001362037 197172163579395468877691)
      ·
        refine ⟨295758245369093203316537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197172163579395468877691 295758245369093203316537)
        ·
          refine ⟨221818684026819902487403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295758245369093203316537 221818684026819902487403)
          ·
            refine ⟨332728026040229853731105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221818684026819902487403 332728026040229853731105)
            ·
              refine ⟨249546019530172390298329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 332728026040229853731105 249546019530172390298329)
              ·
                refine ⟨187159514647629292723747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 249546019530172390298329 187159514647629292723747)
                ·
                  refine ⟨280739271971443939085621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 187159514647629292723747 280739271971443939085621)
                  ·
                    refine ⟨26319306747322869289277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 280739271971443939085621 26319306747322869289277)
                    ·
                      rfl

theorem cell23_153770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_153770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153770 prefixEnd_153770 := by exact prefixLift 153770
  have htrace : WordTrace (prefixWord ++ tailWord_153770) baseStart_153770 baseEnd_153770 := by
    simpa [prefixWord, tailWord_153770, baseEnd_153770] using wordTrace_append hprefix tailTrace_153770
  have hstable : (prefixWord ++ tailWord_153770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153770).length < 2 ^ (prefixWord ++ tailWord_153770).sum := by decide
  have hdescent : baseEnd_153770 < baseStart_153770 := by decide
  rcases family_descends (prefixWord ++ tailWord_153770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153773 : List Nat := [1, 5, 2, 1, 2, 1, 1, 4, 1, 1, 4]
def baseStart_153773 : Nat := 118140960795 + 153773 * 2 ^ 59
def prefixEnd_153773 : Nat := 4983230072969 + 3 ^ 40 * 153773 * 2
def baseEnd_153773 : Nat := 78959460683932096130317

theorem tailTrace_153773 : CollatzResearch.WordTrace tailWord_153773 prefixEnd_153773 78959460683932096130317 := by
  unfold tailWord_153773
  simp only [CollatzResearch.WordTrace]
  refine ⟨5608562071914158182657973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3739041381276105455105315 5608562071914158182657973)
  ·
    refine ⟨525802694241952329624185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5608562071914158182657973 525802694241952329624185)
    ·
      refine ⟨394352020681464247218139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 525802694241952329624185 394352020681464247218139)
      ·
        refine ⟨591528031022196370827209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 394352020681464247218139 591528031022196370827209)
        ·
          refine ⟨443646023266647278120407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 591528031022196370827209 443646023266647278120407)
          ·
            refine ⟨665469034899970917180611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 443646023266647278120407 665469034899970917180611)
            ·
              refine ⟨998203552349956375770917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 665469034899970917180611 998203552349956375770917)
              ·
                refine ⟨187163166065616820457047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 998203552349956375770917 187163166065616820457047)
                ·
                  refine ⟨280744749098425230685571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 187163166065616820457047 280744749098425230685571)
                  ·
                    refine ⟨421117123647637846028357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 280744749098425230685571 421117123647637846028357)
                    ·
                      refine ⟨78959460683932096130317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 421117123647637846028357 78959460683932096130317)
                      ·
                        rfl

theorem cell23_153773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_153773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_153773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_153773 prefixEnd_153773 := by exact prefixLift 153773
  have htrace : WordTrace (prefixWord ++ tailWord_153773) baseStart_153773 baseEnd_153773 := by
    simpa [prefixWord, tailWord_153773, baseEnd_153773] using wordTrace_append hprefix tailTrace_153773
  have hstable : (prefixWord ++ tailWord_153773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153773).length < 2 ^ (prefixWord ++ tailWord_153773).sum := by decide
  have hdescent : baseEnd_153773 < baseStart_153773 := by decide
  rcases family_descends (prefixWord ++ tailWord_153773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
