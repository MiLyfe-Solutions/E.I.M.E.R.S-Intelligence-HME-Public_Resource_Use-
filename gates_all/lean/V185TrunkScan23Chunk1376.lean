import V185TrunkScan23Chunk1375

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8149933 : List Nat := [1, 5, 2, 3, 1, 1, 2, 2, 1, 3, 2]
def baseStart_8149933 : Nat := 118140960795 + 8149933 * 2 ^ 59
def prefixEnd_8149933 : Nat := 4983230072969 + 3 ^ 40 * 8149933 * 2
def baseEnd_8149933 : Nat := 4184832930939367083356647

theorem tailTrace_8149933 : CollatzResearch.WordTrace tailWord_8149933 prefixEnd_8149933 4184832930939367083356647 := by
  unfold tailWord_8149933
  simp only [CollatzResearch.WordTrace]
  refine ⟨297252476783192113586870453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198168317855461409057913635 297252476783192113586870453)
  ·
    refine ⟨27867419698424260648769105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 297252476783192113586870453 27867419698424260648769105)
    ·
      refine ⟨20900564773818195486576829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27867419698424260648769105 20900564773818195486576829)
      ·
        refine ⟨7837711790181823307466311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20900564773818195486576829 7837711790181823307466311)
        ·
          refine ⟨11756567685272734961199467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7837711790181823307466311 11756567685272734961199467)
          ·
            refine ⟨17634851527909102441799201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11756567685272734961199467 17634851527909102441799201)
            ·
              refine ⟨13226138645931826831349401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17634851527909102441799201 13226138645931826831349401)
              ·
                refine ⟨9919603984448870123512051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13226138645931826831349401 9919603984448870123512051)
                ·
                  refine ⟨14879405976673305185268077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9919603984448870123512051 14879405976673305185268077)
                  ·
                    refine ⟨5579777241252489444475529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14879405976673305185268077 5579777241252489444475529)
                    ·
                      refine ⟨4184832930939367083356647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5579777241252489444475529 4184832930939367083356647)
                      ·
                        rfl

theorem cell23_8149933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_8149933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8149933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8149933 prefixEnd_8149933 := by exact prefixLift 8149933
  have htrace : WordTrace (prefixWord ++ tailWord_8149933) baseStart_8149933 baseEnd_8149933 := by
    simpa [prefixWord, tailWord_8149933, baseEnd_8149933] using wordTrace_append hprefix tailTrace_8149933
  have hstable : (prefixWord ++ tailWord_8149933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8149933).length < 2 ^ (prefixWord ++ tailWord_8149933).sum := by decide
  have hdescent : baseEnd_8149933 < baseStart_8149933 := by decide
  rcases family_descends (prefixWord ++ tailWord_8149933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8149952 : List Nat := [2, 1, 1, 2, 3, 3, 3, 3, 5]
def baseStart_8149952 : Nat := 118140960795 + 8149952 * 2 ^ 59
def prefixEnd_8149952 : Nat := 4983230072969 + 3 ^ 40 * 8149952 * 2
def baseEnd_8149952 : Nat := 464982520785755834335451

theorem tailTrace_8149952 : CollatzResearch.WordTrace tailWord_8149952 prefixEnd_8149952 464982520785755834335451 := by
  unfold tailWord_8149952
  simp only [CollatzResearch.WordTrace]
  refine ⟨148626584885061639915906055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198168779846748853221208073 148626584885061639915906055)
  ·
    refine ⟨222939877327592459873859083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148626584885061639915906055 222939877327592459873859083)
    ·
      refine ⟨334409815991388689810788625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222939877327592459873859083 334409815991388689810788625)
      ·
        refine ⟨250807361993541517358091469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334409815991388689810788625 250807361993541517358091469)
        ·
          refine ⟨94052760747578069009284301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250807361993541517358091469 94052760747578069009284301)
          ·
            refine ⟨35269785280341775878481613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94052760747578069009284301 35269785280341775878481613)
            ·
              refine ⟨13226169480128165954430605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35269785280341775878481613 13226169480128165954430605)
              ·
                refine ⟨4959813555048062232911477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13226169480128165954430605 4959813555048062232911477)
                ·
                  refine ⟨464982520785755834335451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4959813555048062232911477 464982520785755834335451)
                  ·
                    rfl

theorem cell23_8149952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 3, 5].length) (baseStart_8149952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8149952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8149952 prefixEnd_8149952 := by exact prefixLift 8149952
  have htrace : WordTrace (prefixWord ++ tailWord_8149952) baseStart_8149952 baseEnd_8149952 := by
    simpa [prefixWord, tailWord_8149952, baseEnd_8149952] using wordTrace_append hprefix tailTrace_8149952
  have hstable : (prefixWord ++ tailWord_8149952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8149952).length < 2 ^ (prefixWord ++ tailWord_8149952).sum := by decide
  have hdescent : baseEnd_8149952 < baseStart_8149952 := by decide
  rcases family_descends (prefixWord ++ tailWord_8149952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8149985 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 6, 1, 4]
def baseStart_8149985 : Nat := 118140960795 + 8149985 * 2 ^ 59
def prefixEnd_8149985 : Nat := 4983230072969 + 3 ^ 40 * 8149985 * 2
def baseEnd_8149985 : Nat := 4184859631933400879906407

theorem tailTrace_8149985 : CollatzResearch.WordTrace tailWord_8149985 prefixEnd_8149985 4184859631933400879906407 := by
  unfold tailWord_8149985
  simp only [CollatzResearch.WordTrace]
  refine ⟨297254373379003726467763409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198169582252669150978508939 297254373379003726467763409)
  ·
    refine ⟨222940780034252794850822557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297254373379003726467763409 222940780034252794850822557)
    ·
      refine ⟨83602792512844798069058459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222940780034252794850822557 83602792512844798069058459)
      ·
        refine ⟨125404188769267197103587689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83602792512844798069058459 125404188769267197103587689)
        ·
          refine ⟨94053141576950397827690767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125404188769267197103587689 94053141576950397827690767)
          ·
            refine ⟨141079712365425596741536151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94053141576950397827690767 141079712365425596741536151)
            ·
              refine ⟨211619568548138395112304227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141079712365425596741536151 211619568548138395112304227)
              ·
                refine ⟨317429352822207592668456341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211619568548138395112304227 317429352822207592668456341)
                ·
                  refine ⟨14879500913540980906333891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 317429352822207592668456341 14879500913540980906333891)
                  ·
                    refine ⟨22319251370311471359500837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14879500913540980906333891 22319251370311471359500837)
                    ·
                      refine ⟨4184859631933400879906407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22319251370311471359500837 4184859631933400879906407)
                      ·
                        rfl

theorem cell23_8149985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_8149985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8149985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8149985 prefixEnd_8149985 := by exact prefixLift 8149985
  have htrace : WordTrace (prefixWord ++ tailWord_8149985) baseStart_8149985 baseEnd_8149985 := by
    simpa [prefixWord, tailWord_8149985, baseEnd_8149985] using wordTrace_append hprefix tailTrace_8149985
  have hstable : (prefixWord ++ tailWord_8149985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8149985).length < 2 ^ (prefixWord ++ tailWord_8149985).sum := by decide
  have hdescent : baseEnd_8149985 < baseStart_8149985 := by decide
  rcases family_descends (prefixWord ++ tailWord_8149985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8150035 : List Nat := [1, 1, 1, 2, 1, 4, 1, 2, 2, 5, 3]
def baseStart_8150035 : Nat := 118140960795 + 8150035 * 2 ^ 59
def prefixEnd_8150035 : Nat := 4983230072969 + 3 ^ 40 * 8150035 * 2
def baseEnd_8150035 : Nat := 4184885305966125684281177

theorem tailTrace_8150035 : CollatzResearch.WordTrace tailWord_8150035 prefixEnd_8150035 4184885305966125684281177 := by
  unfold tailWord_8150035
  simp only [CollatzResearch.WordTrace]
  refine ⟨297256197028822585007083559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198170798019215056671389039 297256197028822585007083559)
  ·
    refine ⟨445884295543233877510625339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297256197028822585007083559 445884295543233877510625339)
    ·
      refine ⟨668826443314850816265938009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445884295543233877510625339 668826443314850816265938009)
      ·
        refine ⟨501619832486138112199453507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 668826443314850816265938009 501619832486138112199453507)
        ·
          refine ⟨752429748729207168299180261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501619832486138112199453507 752429748729207168299180261)
          ·
            refine ⟨141080577886726344056096299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 752429748729207168299180261 141080577886726344056096299)
            ·
              refine ⟨211620866830089516084144449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141080577886726344056096299 211620866830089516084144449)
              ·
                refine ⟨158715650122567137063108337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211620866830089516084144449 158715650122567137063108337)
                ·
                  refine ⟨119036737591925352797331253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158715650122567137063108337 119036737591925352797331253)
                  ·
                    refine ⟨11159694149243001824749805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 119036737591925352797331253 11159694149243001824749805)
                    ·
                      refine ⟨4184885305966125684281177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11159694149243001824749805 4184885305966125684281177)
                      ·
                        rfl

theorem cell23_8150035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 5, 3].length) (baseStart_8150035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8150035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8150035 prefixEnd_8150035 := by exact prefixLift 8150035
  have htrace : WordTrace (prefixWord ++ tailWord_8150035) baseStart_8150035 baseEnd_8150035 := by
    simpa [prefixWord, tailWord_8150035, baseEnd_8150035] using wordTrace_append hprefix tailTrace_8150035
  have hstable : (prefixWord ++ tailWord_8150035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8150035).length < 2 ^ (prefixWord ++ tailWord_8150035).sum := by decide
  have hdescent : baseEnd_8150035 < baseStart_8150035 := by decide
  rcases family_descends (prefixWord ++ tailWord_8150035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8150085 : List Nat := [1, 3, 1, 1, 1, 3, 2, 2, 3, 6]
def baseStart_8150085 : Nat := 118140960795 + 8150085 * 2 ^ 59
def prefixEnd_8150085 : Nat := 4983230072969 + 3 ^ 40 * 8150085 * 2
def baseEnd_8150085 : Nat := 1394970326666283496218649

theorem tailTrace_8150085 : CollatzResearch.WordTrace tailWord_8150085 prefixEnd_8150085 1394970326666283496218649 := by
  unfold tailWord_8150085
  simp only [CollatzResearch.WordTrace]
  refine ⟨297258020678641443546403709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198172013785760962364269139 297258020678641443546403709)
  ·
    refine ⟨111471757754490541329901391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297258020678641443546403709 111471757754490541329901391)
    ·
      refine ⟨167207636631735811994852087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111471757754490541329901391 167207636631735811994852087)
      ·
        refine ⟨250811454947603717992278131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167207636631735811994852087 250811454947603717992278131)
        ·
          refine ⟨376217182421405576988417197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250811454947603717992278131 376217182421405576988417197)
          ·
            refine ⟨141081443408027091370656449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 376217182421405576988417197 141081443408027091370656449)
            ·
              refine ⟨105811082556020318527992337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141081443408027091370656449 105811082556020318527992337)
              ·
                refine ⟨79358311917015238895994253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105811082556020318527992337 79358311917015238895994253)
                ·
                  refine ⟨29759366968880714585997845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79358311917015238895994253 29759366968880714585997845)
                  ·
                    refine ⟨1394970326666283496218649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29759366968880714585997845 1394970326666283496218649)
                    ·
                      rfl

theorem cell23_8150085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 6].length) (baseStart_8150085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8150085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8150085 prefixEnd_8150085 := by exact prefixLift 8150085
  have htrace : WordTrace (prefixWord ++ tailWord_8150085) baseStart_8150085 baseEnd_8150085 := by
    simpa [prefixWord, tailWord_8150085, baseEnd_8150085] using wordTrace_append hprefix tailTrace_8150085
  have hstable : (prefixWord ++ tailWord_8150085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8150085).length < 2 ^ (prefixWord ++ tailWord_8150085).sum := by decide
  have hdescent : baseEnd_8150085 < baseStart_8150085 := by decide
  rcases family_descends (prefixWord ++ tailWord_8150085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8150193 : List Nat := [1, 2, 2, 5, 1, 2, 2, 2, 2, 1, 3]
def baseStart_8150193 : Nat := 118140960795 + 8150193 * 2 ^ 59
def prefixEnd_8150193 : Nat := 4983230072969 + 3 ^ 40 * 8150193 * 2
def baseEnd_8150193 : Nat := 4184966435909536066105451

theorem tailTrace_8150193 : CollatzResearch.WordTrace tailWord_8150193 prefixEnd_8150193 4184966435909536066105451 := by
  unfold tailWord_8150193
  simp only [CollatzResearch.WordTrace]
  refine ⟨297261959762250177991335233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198174639841500118660890155 297261959762250177991335233)
  ·
    refine ⟨222946469821687633493501425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297261959762250177991335233 222946469821687633493501425)
    ·
      refine ⟨167209852366265725120126069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222946469821687633493501425 167209852366265725120126069)
      ·
        refine ⟨15675923659337411730011819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 167209852366265725120126069 15675923659337411730011819)
        ·
          refine ⟨23513885489006117595017729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15675923659337411730011819 23513885489006117595017729)
          ·
            refine ⟨17635414116754588196263297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23513885489006117595017729 17635414116754588196263297)
            ·
              refine ⟨13226560587565941147197473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17635414116754588196263297 13226560587565941147197473)
              ·
                refine ⟨9919920440674455860398105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13226560587565941147197473 9919920440674455860398105)
                ·
                  refine ⟨7439940330505841895298579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9919920440674455860398105 7439940330505841895298579)
                  ·
                    refine ⟨11159910495758762842947869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7439940330505841895298579 11159910495758762842947869)
                    ·
                      refine ⟨4184966435909536066105451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11159910495758762842947869 4184966435909536066105451)
                      ·
                        rfl

theorem cell23_8150193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_8150193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8150193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8150193 prefixEnd_8150193 := by exact prefixLift 8150193
  have htrace : WordTrace (prefixWord ++ tailWord_8150193) baseStart_8150193 baseEnd_8150193 := by
    simpa [prefixWord, tailWord_8150193, baseEnd_8150193] using wordTrace_append hprefix tailTrace_8150193
  have hstable : (prefixWord ++ tailWord_8150193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8150193).length < 2 ^ (prefixWord ++ tailWord_8150193).sum := by decide
  have hdescent : baseEnd_8150193 < baseStart_8150193 := by decide
  rcases family_descends (prefixWord ++ tailWord_8150193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8150199 : List Nat := [1, 1, 3, 1, 4, 1, 1, 2, 3, 4, 2]
def baseStart_8150199 : Nat := 118140960795 + 8150199 * 2 ^ 59
def prefixEnd_8150199 : Nat := 4983230072969 + 3 ^ 40 * 8150199 * 2
def baseEnd_8150199 : Nat := 4184969516793463042630423

theorem tailTrace_8150199 : CollatzResearch.WordTrace tailWord_8150199 prefixEnd_8150199 4184969516793463042630423 := by
  unfold tailWord_8150199
  simp only [CollatzResearch.WordTrace]
  refine ⟨297262178600228441016053651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198174785733485627344035767 297262178600228441016053651)
  ·
    refine ⟨445893267900342661524080477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297262178600228441016053651 445893267900342661524080477)
    ·
      refine ⟨167209975462628498071530179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 445893267900342661524080477 167209975462628498071530179)
      ·
        refine ⟨250814963193942747107295269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167209975462628498071530179 250814963193942747107295269)
        ·
          refine ⟨47027805598864265082617863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 250814963193942747107295269 47027805598864265082617863)
          ·
            refine ⟨70541708398296397623926795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47027805598864265082617863 70541708398296397623926795)
            ·
              refine ⟨105812562597444596435890193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70541708398296397623926795 105812562597444596435890193)
              ·
                refine ⟨79359421948083447326917645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105812562597444596435890193 79359421948083447326917645)
                ·
                  refine ⟨29759783230531292747594117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79359421948083447326917645 29759783230531292747594117)
                  ·
                    refine ⟨5579959355724617390173897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29759783230531292747594117 5579959355724617390173897)
                    ·
                      refine ⟨4184969516793463042630423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5579959355724617390173897 4184969516793463042630423)
                      ·
                        rfl

theorem cell23_8150199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 4, 2].length) (baseStart_8150199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8150199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8150199 prefixEnd_8150199 := by exact prefixLift 8150199
  have htrace : WordTrace (prefixWord ++ tailWord_8150199) baseStart_8150199 baseEnd_8150199 := by
    simpa [prefixWord, tailWord_8150199, baseEnd_8150199] using wordTrace_append hprefix tailTrace_8150199
  have hstable : (prefixWord ++ tailWord_8150199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8150199).length < 2 ^ (prefixWord ++ tailWord_8150199).sum := by decide
  have hdescent : baseEnd_8150199 < baseStart_8150199 := by decide
  rcases family_descends (prefixWord ++ tailWord_8150199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8150209 : List Nat := [1, 2, 6, 1, 1, 1, 1, 1, 1, 8]
def baseStart_8150209 : Nat := 118140960795 + 8150209 * 2 ^ 59
def prefixEnd_8150209 : Nat := 4983230072969 + 3 ^ 40 * 8150209 * 2
def baseEnd_8150209 : Nat := 1394991550533336001168459

theorem tailTrace_8150209 : CollatzResearch.WordTrace tailWord_8150209 prefixEnd_8150209 1394991550533336001168459 := by
  unfold tailWord_8150209
  simp only [CollatzResearch.WordTrace]
  refine ⟨297262543330192212723917681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198175028886794808482611787 297262543330192212723917681)
  ·
    refine ⟨222946907497644159542938261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297262543330192212723917681 222946907497644159542938261)
    ·
      refine ⟨10450636288952069978575231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 222946907497644159542938261 10450636288952069978575231)
      ·
        refine ⟨15675954433428104967862847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10450636288952069978575231 15675954433428104967862847)
        ·
          refine ⟨23513931650142157451794271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15675954433428104967862847 23513931650142157451794271)
          ·
            refine ⟨35270897475213236177691407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23513931650142157451794271 35270897475213236177691407)
            ·
              refine ⟨52906346212819854266537111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35270897475213236177691407 52906346212819854266537111)
              ·
                refine ⟨79359519319229781399805667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52906346212819854266537111 79359519319229781399805667)
                ·
                  refine ⟨119039278978844672099708501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79359519319229781399805667 119039278978844672099708501)
                  ·
                    refine ⟨1394991550533336001168459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 119039278978844672099708501 1394991550533336001168459)
                    ·
                      rfl

theorem cell23_8150209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_8150209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8150209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8150209 prefixEnd_8150209 := by exact prefixLift 8150209
  have htrace : WordTrace (prefixWord ++ tailWord_8150209) baseStart_8150209 baseEnd_8150209 := by
    simpa [prefixWord, tailWord_8150209, baseEnd_8150209] using wordTrace_append hprefix tailTrace_8150209
  have hstable : (prefixWord ++ tailWord_8150209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8150209).length < 2 ^ (prefixWord ++ tailWord_8150209).sum := by decide
  have hdescent : baseEnd_8150209 < baseStart_8150209 := by decide
  rcases family_descends (prefixWord ++ tailWord_8150209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8150210 : List Nat := [3, 5, 1, 1, 2, 1, 2, 1, 1, 3, 3]
def baseStart_8150210 : Nat := 118140960795 + 8150210 * 2 ^ 59
def prefixEnd_8150210 : Nat := 4983230072969 + 3 ^ 40 * 8150210 * 2
def baseEnd_8150210 : Nat := 4184975165080662499592873

theorem tailTrace_8150210 : CollatzResearch.WordTrace tailWord_8150210 prefixEnd_8150210 4184975165080662499592873 := by
  unfold tailWord_8150210
  simp only [CollatzResearch.WordTrace]
  refine ⟨74315644950797147473676021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198175053202125726596469389 74315644950797147473676021)
  ·
    refine ⟨6967091714137232575657127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74315644950797147473676021 6967091714137232575657127)
    ·
      refine ⟨10450637571205848863485691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6967091714137232575657127 10450637571205848863485691)
      ·
        refine ⟨15675956356808773295228537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10450637571205848863485691 15675956356808773295228537)
        ·
          refine ⟨11756967267606579971421403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15675956356808773295228537 11756967267606579971421403)
          ·
            refine ⟨17635450901409869957132105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11756967267606579971421403 17635450901409869957132105)
            ·
              refine ⟨13226588176057402467849079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17635450901409869957132105 13226588176057402467849079)
              ·
                refine ⟨19839882264086103701773619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13226588176057402467849079 19839882264086103701773619)
                ·
                  refine ⟨29759823396129155552660429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19839882264086103701773619 29759823396129155552660429)
                  ·
                    refine ⟨11159933773548433332247661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29759823396129155552660429 11159933773548433332247661)
                    ·
                      refine ⟨4184975165080662499592873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11159933773548433332247661 4184975165080662499592873)
                      ·
                        rfl

theorem cell23_8150210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_8150210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8150210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8150210 prefixEnd_8150210 := by exact prefixLift 8150210
  have htrace : WordTrace (prefixWord ++ tailWord_8150210) baseStart_8150210 baseEnd_8150210 := by
    simpa [prefixWord, tailWord_8150210, baseEnd_8150210] using wordTrace_append hprefix tailTrace_8150210
  have hstable : (prefixWord ++ tailWord_8150210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8150210).length < 2 ^ (prefixWord ++ tailWord_8150210).sum := by decide
  have hdescent : baseEnd_8150210 < baseStart_8150210 := by decide
  rcases family_descends (prefixWord ++ tailWord_8150210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8150237 : List Nat := [1, 4, 3, 2, 2, 2, 2, 1, 1, 3, 2]
def baseStart_8150237 : Nat := 118140960795 + 8150237 * 2 ^ 59
def prefixEnd_8150237 : Nat := 4983230072969 + 3 ^ 40 * 8150237 * 2
def baseEnd_8150237 : Nat := 4184989029058333893955249

theorem tailTrace_8150237 : CollatzResearch.WordTrace tailWord_8150237 prefixEnd_8150237 4184989029058333893955249 := by
  unfold tailWord_8150237
  simp only [CollatzResearch.WordTrace]
  refine ⟨297263564574090773505936965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198175709716060515670624643 297263564574090773505936965)
  ·
    refine ⟨55736918357642020032363181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 297263564574090773505936965 55736918357642020032363181)
    ·
      refine ⟨20901344384115757512136193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55736918357642020032363181 20901344384115757512136193)
      ·
        refine ⟨15676008288086818134102145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20901344384115757512136193 15676008288086818134102145)
        ·
          refine ⟨11757006216065113600576609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15676008288086818134102145 11757006216065113600576609)
          ·
            refine ⟨8817754662048835200432457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11757006216065113600576609 8817754662048835200432457)
            ·
              refine ⟨6613315996536626400324343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8817754662048835200432457 6613315996536626400324343)
              ·
                refine ⟨9919973994804939600486515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6613315996536626400324343 9919973994804939600486515)
                ·
                  refine ⟨14879960992207409400729773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9919973994804939600486515 14879960992207409400729773)
                  ·
                    refine ⟨5579985372077778525273665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14879960992207409400729773 5579985372077778525273665)
                    ·
                      refine ⟨4184989029058333893955249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5579985372077778525273665 4184989029058333893955249)
                      ·
                        rfl

theorem cell23_8150237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_8150237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8150237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8150237 prefixEnd_8150237 := by exact prefixLift 8150237
  have htrace : WordTrace (prefixWord ++ tailWord_8150237) baseStart_8150237 baseEnd_8150237 := by
    simpa [prefixWord, tailWord_8150237, baseEnd_8150237] using wordTrace_append hprefix tailTrace_8150237
  have hstable : (prefixWord ++ tailWord_8150237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8150237).length < 2 ^ (prefixWord ++ tailWord_8150237).sum := by decide
  have hdescent : baseEnd_8150237 < baseStart_8150237 := by decide
  rcases family_descends (prefixWord ++ tailWord_8150237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8150239 : List Nat := [1, 1, 2, 3, 2, 1, 3, 5, 5]
def baseStart_8150239 : Nat := 118140960795 + 8150239 * 2 ^ 59
def prefixEnd_8150239 : Nat := 4983230072969 + 3 ^ 40 * 8150239 * 2
def baseEnd_8150239 : Nat := 464998895113293654014471

theorem tailTrace_8150239 : CollatzResearch.WordTrace tailWord_8150239 prefixEnd_8150239 464998895113293654014471 := by
  unfold tailWord_8150239
  simp only [CollatzResearch.WordTrace]
  refine ⟨297263637520083527847509771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198175758346722351898339847 297263637520083527847509771)
  ·
    refine ⟨445895456280125291771264657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297263637520083527847509771 445895456280125291771264657)
    ·
      refine ⟨334421592210093968828448493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445895456280125291771264657 334421592210093968828448493)
      ·
        refine ⟨125408097078785238310668185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334421592210093968828448493 125408097078785238310668185)
        ·
          refine ⟨94056072809088928733001139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125408097078785238310668185 94056072809088928733001139)
          ·
            refine ⟨141084109213633393099501709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94056072809088928733001139 141084109213633393099501709)
            ·
              refine ⟨52906540955112522412313141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141084109213633393099501709 52906540955112522412313141)
              ·
                refine ⟨4959988214541798976154357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52906540955112522412313141 4959988214541798976154357)
                ·
                  refine ⟨464998895113293654014471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4959988214541798976154357 464998895113293654014471)
                  ·
                    rfl

theorem cell23_8150239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 5, 5].length) (baseStart_8150239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8150239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8150239 prefixEnd_8150239 := by exact prefixLift 8150239
  have htrace : WordTrace (prefixWord ++ tailWord_8150239) baseStart_8150239 baseEnd_8150239 := by
    simpa [prefixWord, tailWord_8150239, baseEnd_8150239] using wordTrace_append hprefix tailTrace_8150239
  have hstable : (prefixWord ++ tailWord_8150239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8150239).length < 2 ^ (prefixWord ++ tailWord_8150239).sum := by decide
  have hdescent : baseEnd_8150239 < baseStart_8150239 := by decide
  rcases family_descends (prefixWord ++ tailWord_8150239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8150250 : List Nat := [3, 1, 3, 1, 1, 5, 1, 2, 2, 2, 2]
def baseStart_8150250 : Nat := 118140960795 + 8150250 * 2 ^ 59
def prefixEnd_8150250 : Nat := 4983230072969 + 3 ^ 40 * 8150250 * 2
def baseEnd_8150250 : Nat := 4184995704306842343092689

theorem tailTrace_8150250 : CollatzResearch.WordTrace tailWord_8150250 prefixEnd_8150250 4184995704306842343092689 := by
  unfold tailWord_8150250
  simp only [CollatzResearch.WordTrace]
  refine ⟨74316009680760919181540051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198176025815362451150773469 74316009680760919181540051)
  ·
    refine ⟨111474014521141378772310077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74316009680760919181540051 111474014521141378772310077)
    ·
      refine ⟨41802755445428017039616279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111474014521141378772310077 41802755445428017039616279)
      ·
        refine ⟨62704133168142025559424419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41802755445428017039616279 62704133168142025559424419)
        ·
          refine ⟨94056199752213038339136629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62704133168142025559424419 94056199752213038339136629)
          ·
            refine ⟨8817768726769972344294059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94056199752213038339136629 8817768726769972344294059)
            ·
              refine ⟨13226653090154958516441089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8817768726769972344294059 13226653090154958516441089)
              ·
                refine ⟨9919989817616218887330817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13226653090154958516441089 9919989817616218887330817)
                ·
                  refine ⟨7439992363212164165498113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9919989817616218887330817 7439992363212164165498113)
                  ·
                    refine ⟨5579994272409123124123585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7439992363212164165498113 5579994272409123124123585)
                    ·
                      refine ⟨4184995704306842343092689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5579994272409123124123585 4184995704306842343092689)
                      ·
                        rfl

theorem cell23_8150250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 2, 2, 2, 2].length) (baseStart_8150250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8150250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8150250 prefixEnd_8150250 := by exact prefixLift 8150250
  have htrace : WordTrace (prefixWord ++ tailWord_8150250) baseStart_8150250 baseEnd_8150250 := by
    simpa [prefixWord, tailWord_8150250, baseEnd_8150250] using wordTrace_append hprefix tailTrace_8150250
  have hstable : (prefixWord ++ tailWord_8150250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8150250).length < 2 ^ (prefixWord ++ tailWord_8150250).sum := by decide
  have hdescent : baseEnd_8150250 < baseStart_8150250 := by decide
  rcases family_descends (prefixWord ++ tailWord_8150250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8150282 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 1, 10]
def baseStart_8150282 : Nat := 118140960795 + 8150282 * 2 ^ 59
def prefixEnd_8150282 : Nat := 4983230072969 + 3 ^ 40 * 8150282 * 2
def baseEnd_8150282 : Nat := 1395004045229262072630847

theorem tailTrace_8150282 : CollatzResearch.WordTrace tailWord_8150282 prefixEnd_8150282 1395004045229262072630847 := by
  unfold tailWord_8150282
  simp only [CollatzResearch.WordTrace]
  refine ⟨74316301464731936547831275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198176803905951830794216733 74316301464731936547831275)
  ·
    refine ⟨111474452197097904821746913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74316301464731936547831275 111474452197097904821746913)
    ·
      refine ⟨83605839147823428616310185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111474452197097904821746913 83605839147823428616310185)
      ·
        refine ⟨62704379360867571462232639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83605839147823428616310185 62704379360867571462232639)
        ·
          refine ⟨94056569041301357193348959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62704379360867571462232639 94056569041301357193348959)
          ·
            refine ⟨141084853561952035790023439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94056569041301357193348959 141084853561952035790023439)
            ·
              refine ⟨211627280342928053685035159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141084853561952035790023439 211627280342928053685035159)
              ·
                refine ⟨317440920514392080527552739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211627280342928053685035159 317440920514392080527552739)
                ·
                  refine ⟨476161380771588120791329109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 317440920514392080527552739 476161380771588120791329109)
                  ·
                    refine ⟨1395004045229262072630847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 476161380771588120791329109 1395004045229262072630847)
                    ·
                      rfl

theorem cell23_8150282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_8150282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8150282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8150282 prefixEnd_8150282 := by exact prefixLift 8150282
  have htrace : WordTrace (prefixWord ++ tailWord_8150282) baseStart_8150282 baseEnd_8150282 := by
    simpa [prefixWord, tailWord_8150282, baseEnd_8150282] using wordTrace_append hprefix tailTrace_8150282
  have hstable : (prefixWord ++ tailWord_8150282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8150282).length < 2 ^ (prefixWord ++ tailWord_8150282).sum := by decide
  have hdescent : baseEnd_8150282 < baseStart_8150282 := by decide
  rcases family_descends (prefixWord ++ tailWord_8150282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8150289 : List Nat := [1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 4]
def baseStart_8150289 : Nat := 118140960795 + 8150289 * 2 ^ 59
def prefixEnd_8150289 : Nat := 4983230072969 + 3 ^ 40 * 8150289 * 2
def baseEnd_8150289 : Nat := 4185015730052367690505009

theorem tailTrace_8150289 : CollatzResearch.WordTrace tailWord_8150289 prefixEnd_8150289 4185015730052367690505009 := by
  unfold tailWord_8150289
  simp only [CollatzResearch.WordTrace]
  refine ⟨297265461169902386386829921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198176974113268257591219947 297265461169902386386829921)
  ·
    refine ⟨222949095877426789790122441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297265461169902386386829921 222949095877426789790122441)
    ·
      refine ⟨167211821908070092342591831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222949095877426789790122441 167211821908070092342591831)
      ·
        refine ⟨250817732862105138513887747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167211821908070092342591831 250817732862105138513887747)
        ·
          refine ⟨376226599293157707770831621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250817732862105138513887747 376226599293157707770831621)
          ·
            refine ⟨70542487367467070207030929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 376226599293157707770831621 70542487367467070207030929)
            ·
              refine ⟨52906865525600302655273197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70542487367467070207030929 52906865525600302655273197)
              ·
                refine ⟨19840074572100113495727449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52906865525600302655273197 19840074572100113495727449)
                ·
                  refine ⟨14880055929075085121795587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19840074572100113495727449 14880055929075085121795587)
                  ·
                    refine ⟨22320083893612627682693381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14880055929075085121795587 22320083893612627682693381)
                    ·
                      refine ⟨4185015730052367690505009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22320083893612627682693381 4185015730052367690505009)
                      ·
                        rfl

theorem cell23_8150289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 4].length) (baseStart_8150289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8150289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8150289 prefixEnd_8150289 := by exact prefixLift 8150289
  have htrace : WordTrace (prefixWord ++ tailWord_8150289) baseStart_8150289 baseEnd_8150289 := by
    simpa [prefixWord, tailWord_8150289, baseEnd_8150289] using wordTrace_append hprefix tailTrace_8150289
  have hstable : (prefixWord ++ tailWord_8150289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8150289).length < 2 ^ (prefixWord ++ tailWord_8150289).sum := by decide
  have hdescent : baseEnd_8150289 < baseStart_8150289 := by decide
  rcases family_descends (prefixWord ++ tailWord_8150289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8150396 : List Nat := [2, 2, 2, 1, 1, 1, 4, 4, 1, 1, 4]
def baseStart_8150396 : Nat := 118140960795 + 8150396 * 2 ^ 59
def prefixEnd_8150396 : Nat := 4983230072969 + 3 ^ 40 * 8150396 * 2
def baseEnd_8150396 : Nat := 4185070672482398771867017

theorem tailTrace_8150396 : CollatzResearch.WordTrace tailWord_8150396 prefixEnd_8150396 4185070672482398771867017 := by
  unfold tailWord_8150396
  simp only [CollatzResearch.WordTrace]
  refine ⟨148634681890257371830487521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198179575853676495773983361 148634681890257371830487521)
  ·
    refine ⟨111476011417693028872865641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148634681890257371830487521 111476011417693028872865641)
    ·
      refine ⟨83607008563269771654649231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111476011417693028872865641 83607008563269771654649231)
      ·
        refine ⟨125410512844904657481973847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83607008563269771654649231 125410512844904657481973847)
        ·
          refine ⟨188115769267356986222960771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125410512844904657481973847 188115769267356986222960771)
          ·
            refine ⟨282173653901035479334441157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188115769267356986222960771 282173653901035479334441157)
            ·
              refine ⟨52907560106444152375207717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 282173653901035479334441157 52907560106444152375207717)
              ·
                refine ⟨9920167519958278570351447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52907560106444152375207717 9920167519958278570351447)
                ·
                  refine ⟨14880251279937417855527171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9920167519958278570351447 14880251279937417855527171)
                  ·
                    refine ⟨22320376919906126783290757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14880251279937417855527171 22320376919906126783290757)
                    ·
                      refine ⟨4185070672482398771867017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22320376919906126783290757 4185070672482398771867017)
                      ·
                        rfl

theorem cell23_8150396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 4, 1, 1, 4].length) (baseStart_8150396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8150396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8150396 prefixEnd_8150396 := by exact prefixLift 8150396
  have htrace : WordTrace (prefixWord ++ tailWord_8150396) baseStart_8150396 baseEnd_8150396 := by
    simpa [prefixWord, tailWord_8150396, baseEnd_8150396] using wordTrace_append hprefix tailTrace_8150396
  have hstable : (prefixWord ++ tailWord_8150396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8150396).length < 2 ^ (prefixWord ++ tailWord_8150396).sum := by decide
  have hdescent : baseEnd_8150396 < baseStart_8150396 := by decide
  rcases family_descends (prefixWord ++ tailWord_8150396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8150440 : List Nat := [2, 1, 6, 1, 2, 2, 1, 1, 1, 6]
def baseStart_8150440 : Nat := 118140960795 + 8150440 * 2 ^ 59
def prefixEnd_8150440 : Nat := 4983230072969 + 3 ^ 40 * 8150440 * 2
def baseEnd_8150440 : Nat := 1395031088543732199905605

theorem tailTrace_8150440 : CollatzResearch.WordTrace tailWord_8150440 prefixEnd_8150440 1395031088543732199905605 := by
  unfold tailWord_8150440
  simp only [CollatzResearch.WordTrace]
  refine ⟨148635484296177669587788387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198180645728236892783717849 148635484296177669587788387)
  ·
    refine ⟨222953226444266504381682581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148635484296177669587788387 222953226444266504381682581)
    ·
      refine ⟨10450932489574992392891371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 222953226444266504381682581 10450932489574992392891371)
      ·
        refine ⟨15676398734362488589337057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10450932489574992392891371 15676398734362488589337057)
        ·
          refine ⟨11757299050771866442002793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15676398734362488589337057 11757299050771866442002793)
          ·
            refine ⟨8817974288078899831502095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11757299050771866442002793 8817974288078899831502095)
            ·
              refine ⟨13226961432118349747253143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8817974288078899831502095 13226961432118349747253143)
              ·
                refine ⟨19840442148177524620879715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13226961432118349747253143 19840442148177524620879715)
                ·
                  refine ⟨29760663222266286931319573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19840442148177524620879715 29760663222266286931319573)
                  ·
                    refine ⟨1395031088543732199905605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29760663222266286931319573 1395031088543732199905605)
                    ·
                      rfl

theorem cell23_8150440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_8150440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8150440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8150440 prefixEnd_8150440 := by exact prefixLift 8150440
  have htrace : WordTrace (prefixWord ++ tailWord_8150440) baseStart_8150440 baseEnd_8150440 := by
    simpa [prefixWord, tailWord_8150440, baseEnd_8150440] using wordTrace_append hprefix tailTrace_8150440
  have hstable : (prefixWord ++ tailWord_8150440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8150440).length < 2 ^ (prefixWord ++ tailWord_8150440).sum := by decide
  have hdescent : baseEnd_8150440 < baseStart_8150440 := by decide
  rcases family_descends (prefixWord ++ tailWord_8150440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8150453 : List Nat := [1, 3, 3, 2, 2, 3, 2, 7]
def baseStart_8150453 : Nat := 118140960795 + 8150453 * 2 ^ 59
def prefixEnd_8150453 : Nat := 4983230072969 + 3 ^ 40 * 8150453 * 2
def baseEnd_8150453 : Nat := 155003701514063149957565

theorem tailTrace_8150453 : CollatzResearch.WordTrace tailWord_8150453 prefixEnd_8150453 155003701514063149957565 := by
  unfold tailWord_8150453
  simp only [CollatzResearch.WordTrace]
  refine ⟨297271442741308242395800013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198180961827538828263866675 297271442741308242395800013)
  ·
    refine ⟨111476791027990590898425005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297271442741308242395800013 111476791027990590898425005)
    ·
      refine ⟨41803796635496471586909377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111476791027990590898425005 41803796635496471586909377)
      ·
        refine ⟨31352847476622353690182033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41803796635496471586909377 31352847476622353690182033)
        ·
          refine ⟨23514635607466765267636525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31352847476622353690182033 23514635607466765267636525)
          ·
            refine ⟨8817988352800036975363697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23514635607466765267636525 8817988352800036975363697)
            ·
              refine ⟨6613491264600027731522773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8817988352800036975363697 6613491264600027731522773)
              ·
                refine ⟨155003701514063149957565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6613491264600027731522773 155003701514063149957565)
                ·
                  rfl

theorem cell23_8150453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 7].length) (baseStart_8150453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8150453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8150453 prefixEnd_8150453 := by exact prefixLift 8150453
  have htrace : WordTrace (prefixWord ++ tailWord_8150453) baseStart_8150453 baseEnd_8150453 := by
    simpa [prefixWord, tailWord_8150453, baseEnd_8150453] using wordTrace_append hprefix tailTrace_8150453
  have hstable : (prefixWord ++ tailWord_8150453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8150453).length < 2 ^ (prefixWord ++ tailWord_8150453).sum := by decide
  have hdescent : baseEnd_8150453 < baseStart_8150453 := by decide
  rcases family_descends (prefixWord ++ tailWord_8150453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8150479 : List Nat := [1, 1, 2, 1, 1, 4, 2, 1, 4, 6]
def baseStart_8150479 : Nat := 118140960795 + 8150479 * 2 ^ 59
def prefixEnd_8150479 : Nat := 4983230072969 + 3 ^ 40 * 8150479 * 2
def baseEnd_8150479 : Nat := 1395037763792240649043045

theorem tailTrace_8150479 : CollatzResearch.WordTrace tailWord_8150479 prefixEnd_8150479 1395037763792240649043045 := by
  unfold tailWord_8150479
  simp only [CollatzResearch.WordTrace]
  refine ⟨297272391039214048836246491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198181594026142699224164327 297272391039214048836246491)
  ·
    refine ⟨445908586558821073254369737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297272391039214048836246491 445908586558821073254369737)
    ·
      refine ⟨334431439919115804940777303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445908586558821073254369737 334431439919115804940777303)
      ·
        refine ⟨501647159878673707411165955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334431439919115804940777303 501647159878673707411165955)
        ·
          refine ⟨752470739818010561116748933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501647159878673707411165955 752470739818010561116748933)
          ·
            refine ⟨141088263715876980209390425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 752470739818010561116748933 141088263715876980209390425)
            ·
              refine ⟨105816197786907735157042819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141088263715876980209390425 105816197786907735157042819)
              ·
                refine ⟨158724296680361602735564229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105816197786907735157042819 158724296680361602735564229)
                ·
                  refine ⟨29760805627567800512918293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158724296680361602735564229 29760805627567800512918293)
                  ·
                    refine ⟨1395037763792240649043045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29760805627567800512918293 1395037763792240649043045)
                    ·
                      rfl

theorem cell23_8150479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 6].length) (baseStart_8150479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8150479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8150479 prefixEnd_8150479 := by exact prefixLift 8150479
  have htrace : WordTrace (prefixWord ++ tailWord_8150479) baseStart_8150479 baseEnd_8150479 := by
    simpa [prefixWord, tailWord_8150479, baseEnd_8150479] using wordTrace_append hprefix tailTrace_8150479
  have hstable : (prefixWord ++ tailWord_8150479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8150479).length < 2 ^ (prefixWord ++ tailWord_8150479).sum := by decide
  have hdescent : baseEnd_8150479 < baseStart_8150479 := by decide
  rcases family_descends (prefixWord ++ tailWord_8150479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8150497 : List Nat := [1, 2, 3, 1, 2, 5, 2, 1, 2, 1, 3]
def baseStart_8150497 : Nat := 118140960795 + 8150497 * 2 ^ 59
def prefixEnd_8150497 : Nat := 4983230072969 + 3 ^ 40 * 8150497 * 2
def baseEnd_8150497 : Nat := 4185122534028502876704053

theorem tailTrace_8150497 : CollatzResearch.WordTrace tailWord_8150497 prefixEnd_8150497 4185122534028502876704053 := by
  unfold tailWord_8150497
  simp only [CollatzResearch.WordTrace]
  refine ⟨297273047553148837910401745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198182031702099225273601163 297273047553148837910401745)
  ·
    refine ⟨222954785664861628432801309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297273047553148837910401745 222954785664861628432801309)
    ·
      refine ⟨83608044624323110662300491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222954785664861628432801309 83608044624323110662300491)
      ·
        refine ⟨125412066936484665993450737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83608044624323110662300491 125412066936484665993450737)
        ·
          refine ⟨94059050202363499495088053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125412066936484665993450737 94059050202363499495088053)
          ·
            refine ⟨8818035956471578077664505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94059050202363499495088053 8818035956471578077664505)
            ·
              refine ⟨6613526967353683558248379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8818035956471578077664505 6613526967353683558248379)
              ·
                refine ⟨9920290451030525337372569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6613526967353683558248379 9920290451030525337372569)
                ·
                  refine ⟨7440217838272894003029427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9920290451030525337372569 7440217838272894003029427)
                  ·
                    refine ⟨11160326757409341004544141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7440217838272894003029427 11160326757409341004544141)
                    ·
                      refine ⟨4185122534028502876704053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11160326757409341004544141 4185122534028502876704053)
                      ·
                        rfl

theorem cell23_8150497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 1, 2, 1, 3].length) (baseStart_8150497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8150497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8150497 prefixEnd_8150497 := by exact prefixLift 8150497
  have htrace : WordTrace (prefixWord ++ tailWord_8150497) baseStart_8150497 baseEnd_8150497 := by
    simpa [prefixWord, tailWord_8150497, baseEnd_8150497] using wordTrace_append hprefix tailTrace_8150497
  have hstable : (prefixWord ++ tailWord_8150497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8150497).length < 2 ^ (prefixWord ++ tailWord_8150497).sum := by decide
  have hdescent : baseEnd_8150497 < baseStart_8150497 := by decide
  rcases family_descends (prefixWord ++ tailWord_8150497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8150519 : List Nat := [1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 7]
def baseStart_8150519 : Nat := 118140960795 + 8150519 * 2 ^ 59
def prefixEnd_8150519 : Nat := 4983230072969 + 3 ^ 40 * 8150519 * 2
def baseEnd_8150519 : Nat := 4185133830602901790628951

theorem tailTrace_8150519 : CollatzResearch.WordTrace tailWord_8150519 prefixEnd_8150519 4185133830602901790628951 := by
  unfold tailWord_8150519
  simp only [CollatzResearch.WordTrace]
  refine ⟨297273849959069135667702611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198182566639379423778468407 297273849959069135667702611)
  ·
    refine ⟨445910774938603703501553917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297273849959069135667702611 445910774938603703501553917)
    ·
      refine ⟨167216540601976388813082719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 445910774938603703501553917 167216540601976388813082719)
      ·
        refine ⟨250824810902964583219624079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167216540601976388813082719 250824810902964583219624079)
        ·
          refine ⟨376237216354446874829436119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250824810902964583219624079 376237216354446874829436119)
          ·
            refine ⟨564355824531670312244154179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376237216354446874829436119 564355824531670312244154179)
            ·
              refine ⟨846533736797505468366231269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 564355824531670312244154179 846533736797505468366231269)
              ·
                refine ⟨158725075649532275318668363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 846533736797505468366231269 158725075649532275318668363)
                ·
                  refine ⟨238087613474298412978002545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158725075649532275318668363 238087613474298412978002545)
                  ·
                    refine ⟨178565710105723809733501909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 238087613474298412978002545 178565710105723809733501909)
                    ·
                      refine ⟨4185133830602901790628951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 178565710105723809733501909 4185133830602901790628951)
                      ·
                        rfl

theorem cell23_8150519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 7].length) (baseStart_8150519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8150519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8150519 prefixEnd_8150519 := by exact prefixLift 8150519
  have htrace : WordTrace (prefixWord ++ tailWord_8150519) baseStart_8150519 baseEnd_8150519 := by
    simpa [prefixWord, tailWord_8150519, baseEnd_8150519] using wordTrace_append hprefix tailTrace_8150519
  have hstable : (prefixWord ++ tailWord_8150519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8150519).length < 2 ^ (prefixWord ++ tailWord_8150519).sum := by decide
  have hdescent : baseEnd_8150519 < baseStart_8150519 := by decide
  rcases family_descends (prefixWord ++ tailWord_8150519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8150556 : List Nat := [2, 2, 3, 1, 2, 1, 2, 2, 1, 7]
def baseStart_8150556 : Nat := 118140960795 + 8150556 * 2 ^ 59
def prefixEnd_8150556 : Nat := 4983230072969 + 3 ^ 40 * 8150556 * 2
def baseEnd_8150556 : Nat := 1395050943129039381955427

theorem tailTrace_8150556 : CollatzResearch.WordTrace tailWord_8150556 prefixEnd_8150556 1395050943129039381955427 := by
  unfold tailWord_8150556
  simp only [CollatzResearch.WordTrace]
  refine ⟨148637599729967545493399761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198183466306623393991199681 148637599729967545493399761)
  ·
    refine ⟨111478199797475659120049821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148637599729967545493399761 111478199797475659120049821)
    ·
      refine ⟨41804324924053372170018683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111478199797475659120049821 41804324924053372170018683)
      ·
        refine ⟨62706487386080058255028025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41804324924053372170018683 62706487386080058255028025)
        ·
          refine ⟨47029865539560043691271019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62706487386080058255028025 47029865539560043691271019)
          ·
            refine ⟨70544798309340065536906529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47029865539560043691271019 70544798309340065536906529)
            ·
              refine ⟨52908598732005049152679897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70544798309340065536906529 52908598732005049152679897)
              ·
                refine ⟨39681449049003786864509923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52908598732005049152679897 39681449049003786864509923)
                ·
                  refine ⟨59522173573505680296764885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39681449049003786864509923 59522173573505680296764885)
                  ·
                    refine ⟨1395050943129039381955427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59522173573505680296764885 1395050943129039381955427)
                    ·
                      rfl

theorem cell23_8150556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_8150556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8150556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8150556 prefixEnd_8150556 := by exact prefixLift 8150556
  have htrace : WordTrace (prefixWord ++ tailWord_8150556) baseStart_8150556 baseEnd_8150556 := by
    simpa [prefixWord, tailWord_8150556, baseEnd_8150556] using wordTrace_append hprefix tailTrace_8150556
  have hstable : (prefixWord ++ tailWord_8150556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8150556).length < 2 ^ (prefixWord ++ tailWord_8150556).sum := by decide
  have hdescent : baseEnd_8150556 < baseStart_8150556 := by decide
  rcases family_descends (prefixWord ++ tailWord_8150556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8150593 : List Nat := [1, 2, 5, 1, 1, 1, 2, 1, 4, 1, 4]
def baseStart_8150593 : Nat := 118140960795 + 8150593 * 2 ^ 59
def prefixEnd_8150593 : Nat := 4983230072969 + 3 ^ 40 * 8150593 * 2
def baseEnd_8150593 : Nat := 4185171828171334501103611

theorem tailTrace_8150593 : CollatzResearch.WordTrace tailWord_8150593 prefixEnd_8150593 4185171828171334501103611 := by
  unfold tailWord_8150593
  simp only [CollatzResearch.WordTrace]
  refine ⟨297276548960801046305896433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198184365973867364203930955 297276548960801046305896433)
  ·
    refine ⟨222957411720600784729422325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297276548960801046305896433 222957411720600784729422325)
    ·
      refine ⟨20902257348806323568383343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 222957411720600784729422325 20902257348806323568383343)
      ·
        refine ⟨31353386023209485352575015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20902257348806323568383343 31353386023209485352575015)
        ·
          refine ⟨47030079034814228028862523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31353386023209485352575015 47030079034814228028862523)
          ·
            refine ⟨70545118552221342043293785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47030079034814228028862523 70545118552221342043293785)
            ·
              refine ⟨52908838914166006532470339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70545118552221342043293785 52908838914166006532470339)
              ·
                refine ⟨79363258371249009798705509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52908838914166006532470339 79363258371249009798705509)
                ·
                  refine ⟨14880610944609189337257283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79363258371249009798705509 14880610944609189337257283)
                  ·
                    refine ⟨22320916416913784005885925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14880610944609189337257283 22320916416913784005885925)
                    ·
                      refine ⟨4185171828171334501103611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22320916416913784005885925 4185171828171334501103611)
                      ·
                        rfl

theorem cell23_8150593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_8150593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8150593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8150593 prefixEnd_8150593 := by exact prefixLift 8150593
  have htrace : WordTrace (prefixWord ++ tailWord_8150593) baseStart_8150593 baseEnd_8150593 := by
    simpa [prefixWord, tailWord_8150593, baseEnd_8150593] using wordTrace_append hprefix tailTrace_8150593
  have hstable : (prefixWord ++ tailWord_8150593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8150593).length < 2 ^ (prefixWord ++ tailWord_8150593).sum := by decide
  have hdescent : baseEnd_8150593 < baseStart_8150593 := by decide
  rcases family_descends (prefixWord ++ tailWord_8150593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8150606 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 4, 1, 6]
def baseStart_8150606 : Nat := 118140960795 + 8150606 * 2 ^ 59
def prefixEnd_8150606 : Nat := 4983230072969 + 3 ^ 40 * 8150606 * 2
def baseEnd_8150606 : Nat := 4185178503419842950241051

theorem tailTrace_8150606 : CollatzResearch.WordTrace tailWord_8150606 prefixEnd_8150606 4185178503419842950241051 := by
  unfold tailWord_8150606
  simp only [CollatzResearch.WordTrace]
  refine ⟨37159627888719243690764959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198184682073169299684079781 37159627888719243690764959)
  ·
    refine ⟨55739441833078865536147439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37159627888719243690764959 55739441833078865536147439)
    ·
      refine ⟨83609162749618298304221159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55739441833078865536147439 83609162749618298304221159)
      ·
        refine ⟨125413744124427447456331739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83609162749618298304221159 125413744124427447456331739)
        ·
          refine ⟨188120616186641171184497609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125413744124427447456331739 188120616186641171184497609)
          ·
            refine ⟨141090462139980878388373207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188120616186641171184497609 141090462139980878388373207)
            ·
              refine ⟨211635693209971317582559811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141090462139980878388373207 211635693209971317582559811)
              ·
                refine ⟨317453539814956976373839717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211635693209971317582559811 317453539814956976373839717)
                ·
                  refine ⟨59522538715304433070094947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 317453539814956976373839717 59522538715304433070094947)
                  ·
                    refine ⟨89283808072956649605142421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59522538715304433070094947 89283808072956649605142421)
                    ·
                      refine ⟨4185178503419842950241051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89283808072956649605142421 4185178503419842950241051)
                      ·
                        rfl

theorem cell23_8150606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_8150606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8150606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8150606 prefixEnd_8150606 := by exact prefixLift 8150606
  have htrace : WordTrace (prefixWord ++ tailWord_8150606) baseStart_8150606 baseEnd_8150606 := by
    simpa [prefixWord, tailWord_8150606, baseEnd_8150606] using wordTrace_append hprefix tailTrace_8150606
  have hstable : (prefixWord ++ tailWord_8150606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8150606).length < 2 ^ (prefixWord ++ tailWord_8150606).sum := by decide
  have hdescent : baseEnd_8150606 < baseStart_8150606 := by decide
  rcases family_descends (prefixWord ++ tailWord_8150606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8150610 : List Nat := [3, 2, 2, 1, 2, 2, 2, 1, 2, 4, 2]
def baseStart_8150610 : Nat := 118140960795 + 8150610 * 2 ^ 59
def prefixEnd_8150610 : Nat := 4983230072969 + 3 ^ 40 * 8150610 * 2
def baseEnd_8150610 : Nat := 4185180557342460934591033

theorem tailTrace_8150610 : CollatzResearch.WordTrace tailWord_8150610 prefixEnd_8150610 4185180557342460934591033 := by
  unfold tailWord_8150610
  simp only [CollatzResearch.WordTrace]
  refine ⟨74319292250434864552316321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198184779334492972139510189 74319292250434864552316321)
  ·
    refine ⟨55739469187826148414237241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74319292250434864552316321 55739469187826148414237241)
    ·
      refine ⟨41804601890869611310677931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55739469187826148414237241 41804601890869611310677931)
      ·
        refine ⟨62706902836304416966016897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41804601890869611310677931 62706902836304416966016897)
        ·
          refine ⟨47030177127228312724512673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62706902836304416966016897 47030177127228312724512673)
          ·
            refine ⟨35272632845421234543384505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47030177127228312724512673 35272632845421234543384505)
            ·
              refine ⟨26454474634065925907538379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35272632845421234543384505 26454474634065925907538379)
              ·
                refine ⟨39681711951098888861307569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26454474634065925907538379 39681711951098888861307569)
                ·
                  refine ⟨29761283963324166645980677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39681711951098888861307569 29761283963324166645980677)
                  ·
                    refine ⟨5580240743123281246121377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29761283963324166645980677 5580240743123281246121377)
                    ·
                      refine ⟨4185180557342460934591033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5580240743123281246121377 4185180557342460934591033)
                      ·
                        rfl

theorem cell23_8150610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 2, 4, 2].length) (baseStart_8150610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8150610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8150610 prefixEnd_8150610 := by exact prefixLift 8150610
  have htrace : WordTrace (prefixWord ++ tailWord_8150610) baseStart_8150610 baseEnd_8150610 := by
    simpa [prefixWord, tailWord_8150610, baseEnd_8150610] using wordTrace_append hprefix tailTrace_8150610
  have hstable : (prefixWord ++ tailWord_8150610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8150610).length < 2 ^ (prefixWord ++ tailWord_8150610).sum := by decide
  have hdescent : baseEnd_8150610 < baseStart_8150610 := by decide
  rcases family_descends (prefixWord ++ tailWord_8150610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8150620 : List Nat := [2, 2, 4, 1, 2, 1, 2, 2, 3, 4]
def baseStart_8150620 : Nat := 118140960795 + 8150620 * 2 ^ 59
def prefixEnd_8150620 : Nat := 4983230072969 + 3 ^ 40 * 8150620 * 2
def baseEnd_8150620 : Nat := 1395061897383001965155329

theorem tailTrace_8150620 : CollatzResearch.WordTrace tailWord_8150620 prefixEnd_8150620 1395061897383001965155329 := by
  unfold tailWord_8150620
  simp only [CollatzResearch.WordTrace]
  refine ⟨148638766865851614958564657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198185022487802153278086209 148638766865851614958564657)
  ·
    refine ⟨111479075149388711218923493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148638766865851614958564657 111479075149388711218923493)
    ·
      refine ⟨20902326590510383353548155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111479075149388711218923493 20902326590510383353548155)
      ·
        refine ⟨31353489885765575030322233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20902326590510383353548155 31353489885765575030322233)
        ·
          refine ⟨23515117414324181272741675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31353489885765575030322233 23515117414324181272741675)
          ·
            refine ⟨35272676121486271909112513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23515117414324181272741675 35272676121486271909112513)
            ·
              refine ⟨26454507091114703931834385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35272676121486271909112513 26454507091114703931834385)
              ·
                refine ⟨19840880318336027948875789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26454507091114703931834385 19840880318336027948875789)
                ·
                  refine ⟨7440330119376010480828421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19840880318336027948875789 7440330119376010480828421)
                  ·
                    refine ⟨1395061897383001965155329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7440330119376010480828421 1395061897383001965155329)
                    ·
                      rfl

theorem cell23_8150620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_8150620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8150620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8150620 prefixEnd_8150620 := by exact prefixLift 8150620
  have htrace : WordTrace (prefixWord ++ tailWord_8150620) baseStart_8150620 baseEnd_8150620 := by
    simpa [prefixWord, tailWord_8150620, baseEnd_8150620] using wordTrace_append hprefix tailTrace_8150620
  have hstable : (prefixWord ++ tailWord_8150620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8150620).length < 2 ^ (prefixWord ++ tailWord_8150620).sum := by decide
  have hdescent : baseEnd_8150620 < baseStart_8150620 := by decide
  rcases family_descends (prefixWord ++ tailWord_8150620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8150680 : List Nat := [2, 1, 2, 4, 1, 2, 3, 2, 1, 5]
def baseStart_8150680 : Nat := 118140960795 + 8150680 * 2 ^ 59
def prefixEnd_8150680 : Nat := 4983230072969 + 3 ^ 40 * 8150680 * 2
def baseEnd_8150680 : Nat := 1395072166996091886905237

theorem tailTrace_8150680 : CollatzResearch.WordTrace tailWord_8150680 prefixEnd_8150680 1395072166996091886905237 := by
  unfold tailWord_8150680
  simp only [CollatzResearch.WordTrace]
  refine ⟨148639861055742930082156747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198186481407657240109542329 148639861055742930082156747)
  ·
    refine ⟨222959791583614395123235121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148639861055742930082156747 222959791583614395123235121)
    ·
      refine ⟨167219843687710796342426341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222959791583614395123235121 167219843687710796342426341)
      ·
        refine ⟨31353720691445774314204939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167219843687710796342426341 31353720691445774314204939)
        ·
          refine ⟨47030581037168661471307409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31353720691445774314204939 47030581037168661471307409)
          ·
            refine ⟨35272935777876496103480557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47030581037168661471307409 35272935777876496103480557)
            ·
              refine ⟨13227350916703686038805209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35272935777876496103480557 13227350916703686038805209)
              ·
                refine ⟨9920513187527764529103907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13227350916703686038805209 9920513187527764529103907)
                ·
                  refine ⟨14880769781291646793655861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9920513187527764529103907 14880769781291646793655861)
                  ·
                    refine ⟨1395072166996091886905237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14880769781291646793655861 1395072166996091886905237)
                    ·
                      rfl

theorem cell23_8150680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 2, 1, 5].length) (baseStart_8150680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8150680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8150680 prefixEnd_8150680 := by exact prefixLift 8150680
  have htrace : WordTrace (prefixWord ++ tailWord_8150680) baseStart_8150680 baseEnd_8150680 := by
    simpa [prefixWord, tailWord_8150680, baseEnd_8150680] using wordTrace_append hprefix tailTrace_8150680
  have hstable : (prefixWord ++ tailWord_8150680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8150680).length < 2 ^ (prefixWord ++ tailWord_8150680).sum := by decide
  have hdescent : baseEnd_8150680 < baseStart_8150680 := by decide
  rcases family_descends (prefixWord ++ tailWord_8150680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8150693 : List Nat := [1, 3, 1, 2, 1, 2, 2, 1, 6, 4]
def baseStart_8150693 : Nat := 118140960795 + 8150693 * 2 ^ 59
def prefixEnd_8150693 : Nat := 4983230072969 + 3 ^ 40 * 8150693 * 2
def baseEnd_8150693 : Nat := 1395074392078928036617717

theorem tailTrace_8150693 : CollatzResearch.WordTrace tailWord_8150693 prefixEnd_8150693 1395074392078928036617717 := by
  unfold tailWord_8150693
  simp only [CollatzResearch.WordTrace]
  refine ⟨297280196260438763384536733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198186797506959175589691155 297280196260438763384536733)
  ·
    refine ⟨111480073597664536269201275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297280196260438763384536733 111480073597664536269201275)
    ·
      refine ⟨167220110396496804403801913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111480073597664536269201275 167220110396496804403801913)
      ·
        refine ⟨125415082797372603302851435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167220110396496804403801913 125415082797372603302851435)
        ·
          refine ⟨188122624196058904954277153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125415082797372603302851435 188122624196058904954277153)
          ·
            refine ⟨141091968147044178715707865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188122624196058904954277153 141091968147044178715707865)
            ·
              refine ⟨105818976110283134036780899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141091968147044178715707865 105818976110283134036780899)
              ·
                refine ⟨158728464165424701055171349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105818976110283134036780899 158728464165424701055171349)
                ·
                  refine ⟨7440396757754282861961157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 158728464165424701055171349 7440396757754282861961157)
                  ·
                    refine ⟨1395074392078928036617717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7440396757754282861961157 1395074392078928036617717)
                    ·
                      rfl

theorem cell23_8150693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 6, 4].length) (baseStart_8150693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8150693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8150693 prefixEnd_8150693 := by exact prefixLift 8150693
  have htrace : WordTrace (prefixWord ++ tailWord_8150693) baseStart_8150693 baseEnd_8150693 := by
    simpa [prefixWord, tailWord_8150693, baseEnd_8150693] using wordTrace_append hprefix tailTrace_8150693
  have hstable : (prefixWord ++ tailWord_8150693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8150693).length < 2 ^ (prefixWord ++ tailWord_8150693).sum := by decide
  have hdescent : baseEnd_8150693 < baseStart_8150693 := by decide
  rcases family_descends (prefixWord ++ tailWord_8150693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8150711 : List Nat := [1, 1, 3, 1, 5, 3, 2, 2, 1, 1, 3]
def baseStart_8150711 : Nat := 118140960795 + 8150711 * 2 ^ 59
def prefixEnd_8150711 : Nat := 4983230072969 + 3 ^ 40 * 8150711 * 2
def baseEnd_8150711 : Nat := 4185232418888565039428069

theorem tailTrace_8150711 : CollatzResearch.WordTrace tailWord_8150711 prefixEnd_8150711 4185232418888565039428069 := by
  unfold tailWord_8150711
  simp only [CollatzResearch.WordTrace]
  refine ⟨297280852774373552458691987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198187235182915701639127991 297280852774373552458691987)
  ·
    refine ⟨445921279161560328688037981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297280852774373552458691987 445921279161560328688037981)
    ·
      refine ⟨167220479685585123258014243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 445921279161560328688037981 167220479685585123258014243)
      ·
        refine ⟨250830719528377684887021365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167220479685585123258014243 250830719528377684887021365)
        ·
          refine ⟨23515379955785407958158253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 250830719528377684887021365 23515379955785407958158253)
          ·
            refine ⟨8818267483419527984309345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23515379955785407958158253 8818267483419527984309345)
            ·
              refine ⟨6613700612564645988232009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8818267483419527984309345 6613700612564645988232009)
              ·
                refine ⟨4960275459423484491174007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6613700612564645988232009 4960275459423484491174007)
                ·
                  refine ⟨7440413189135226736761011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4960275459423484491174007 7440413189135226736761011)
                  ·
                    refine ⟨11160619783702840105141517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7440413189135226736761011 11160619783702840105141517)
                    ·
                      refine ⟨4185232418888565039428069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11160619783702840105141517 4185232418888565039428069)
                      ·
                        rfl

theorem cell23_8150711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 2, 1, 1, 3].length) (baseStart_8150711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8150711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8150711 prefixEnd_8150711 := by exact prefixLift 8150711
  have htrace : WordTrace (prefixWord ++ tailWord_8150711) baseStart_8150711 baseEnd_8150711 := by
    simpa [prefixWord, tailWord_8150711, baseEnd_8150711] using wordTrace_append hprefix tailTrace_8150711
  have hstable : (prefixWord ++ tailWord_8150711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8150711).length < 2 ^ (prefixWord ++ tailWord_8150711).sum := by decide
  have hdescent : baseEnd_8150711 < baseStart_8150711 := by decide
  rcases family_descends (prefixWord ++ tailWord_8150711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8150717 : List Nat := [1, 4, 1, 2, 1, 2, 2, 3, 3, 2, 2]
def baseStart_8150717 : Nat := 118140960795 + 8150717 * 2 ^ 59
def prefixEnd_8150717 : Nat := 4983230072969 + 3 ^ 40 * 8150717 * 2
def baseEnd_8150717 : Nat := 4185235499772492015953041

theorem tailTrace_8150717 : CollatzResearch.WordTrace tailWord_8150717 prefixEnd_8150717 4185235499772492015953041 := by
  unfold tailWord_8150717
  simp only [CollatzResearch.WordTrace]
  refine ⟨297281071612351815483410405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198187381074901210322273603 297281071612351815483410405)
  ·
    refine ⟨55740200927315965403139451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 297281071612351815483410405 55740200927315965403139451)
    ·
      refine ⟨83610301390973948104709177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55740200927315965403139451 83610301390973948104709177)
      ·
        refine ⟨62707726043230461078531883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83610301390973948104709177 62707726043230461078531883)
        ·
          refine ⟨94061589064845691617797825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62707726043230461078531883 94061589064845691617797825)
          ·
            refine ⟨70546191798634268713348369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94061589064845691617797825 70546191798634268713348369)
            ·
              refine ⟨52909643848975701535011277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70546191798634268713348369 52909643848975701535011277)
              ·
                refine ⟨19841116443365888075629229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52909643848975701535011277 19841116443365888075629229)
                ·
                  refine ⟨7440418666262208028360961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19841116443365888075629229 7440418666262208028360961)
                  ·
                    refine ⟨5580313999696656021270721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7440418666262208028360961 5580313999696656021270721)
                    ·
                      refine ⟨4185235499772492015953041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5580313999696656021270721 4185235499772492015953041)
                      ·
                        rfl

theorem cell23_8150717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 3, 2, 2].length) (baseStart_8150717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8150717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8150717 prefixEnd_8150717 := by exact prefixLift 8150717
  have htrace : WordTrace (prefixWord ++ tailWord_8150717) baseStart_8150717 baseEnd_8150717 := by
    simpa [prefixWord, tailWord_8150717, baseEnd_8150717] using wordTrace_append hprefix tailTrace_8150717
  have hstable : (prefixWord ++ tailWord_8150717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8150717).length < 2 ^ (prefixWord ++ tailWord_8150717).sum := by decide
  have hdescent : baseEnd_8150717 < baseStart_8150717 := by decide
  rcases family_descends (prefixWord ++ tailWord_8150717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8150783 : List Nat := [1, 1, 2, 2, 1, 3, 4, 1, 2, 6]
def baseStart_8150783 : Nat := 118140960795 + 8150783 * 2 ^ 59
def prefixEnd_8150783 : Nat := 4983230072969 + 3 ^ 40 * 8150783 * 2
def baseEnd_8150783 : Nat := 1395089796498562919242579

theorem tailTrace_8150783 : CollatzResearch.WordTrace tailWord_8150783 prefixEnd_8150783 1395089796498562919242579 := by
  unfold tailWord_8150783
  simp only [CollatzResearch.WordTrace]
  refine ⟨297283478830112708755313003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198188985886741805836875335 297283478830112708755313003)
  ·
    refine ⟨445925218245169063132969505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297283478830112708755313003 445925218245169063132969505)
    ·
      refine ⟨334443913683876797349727129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445925218245169063132969505 334443913683876797349727129)
      ·
        refine ⟨250832935262907598012295347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334443913683876797349727129 250832935262907598012295347)
        ·
          refine ⟨376249402894361397018443021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250832935262907598012295347 376249402894361397018443021)
          ·
            refine ⟨141093526085385523881916133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 376249402894361397018443021 141093526085385523881916133)
            ·
              refine ⟨26455036141009785727859275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141093526085385523881916133 26455036141009785727859275)
              ·
                refine ⟨39682554211514678591788913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26455036141009785727859275 39682554211514678591788913)
                ·
                  refine ⟨29761915658636008943841685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39682554211514678591788913 29761915658636008943841685)
                  ·
                    refine ⟨1395089796498562919242579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29761915658636008943841685 1395089796498562919242579)
                    ·
                      rfl

theorem cell23_8150783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 6].length) (baseStart_8150783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8150783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8150783 prefixEnd_8150783 := by exact prefixLift 8150783
  have htrace : WordTrace (prefixWord ++ tailWord_8150783) baseStart_8150783 baseEnd_8150783 := by
    simpa [prefixWord, tailWord_8150783, baseEnd_8150783] using wordTrace_append hprefix tailTrace_8150783
  have hstable : (prefixWord ++ tailWord_8150783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8150783).length < 2 ^ (prefixWord ++ tailWord_8150783).sum := by decide
  have hdescent : baseEnd_8150783 < baseStart_8150783 := by decide
  rcases family_descends (prefixWord ++ tailWord_8150783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8150793 : List Nat := [1, 2, 1, 1, 3, 2, 1, 4, 2, 1, 5]
def baseStart_8150793 : Nat := 118140960795 + 8150793 * 2 ^ 59
def prefixEnd_8150793 : Nat := 4983230072969 + 3 ^ 40 * 8150793 * 2
def baseEnd_8150793 : Nat := 4185274524302233718602691

theorem tailTrace_8150793 : CollatzResearch.WordTrace tailWord_8150793 prefixEnd_8150793 4185274524302233718602691 := by
  unfold tailWord_8150793
  simp only [CollatzResearch.WordTrace]
  refine ⟨297283843560076480463177033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198189229040050986975451355 297283843560076480463177033)
  ·
    refine ⟨222962882670057360347382775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297283843560076480463177033 222962882670057360347382775)
    ·
      refine ⟨334444324005086040521074163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222962882670057360347382775 334444324005086040521074163)
      ·
        refine ⟨501666486007629060781611245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334444324005086040521074163 501666486007629060781611245)
        ·
          refine ⟨188124932252860897793104217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 501666486007629060781611245 188124932252860897793104217)
          ·
            refine ⟨141093699189645673344828163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188124932252860897793104217 141093699189645673344828163)
            ·
              refine ⟨211640548784468510017242245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141093699189645673344828163 211640548784468510017242245)
              ·
                refine ⟨39682602897087845628232921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 211640548784468510017242245 39682602897087845628232921)
                ·
                  refine ⟨29761952172815884221174691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39682602897087845628232921 29761952172815884221174691)
                  ·
                    refine ⟨44642928259223826331762037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29761952172815884221174691 44642928259223826331762037)
                    ·
                      refine ⟨4185274524302233718602691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44642928259223826331762037 4185274524302233718602691)
                      ·
                        rfl

theorem cell23_8150793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 1, 5].length) (baseStart_8150793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8150793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8150793 prefixEnd_8150793 := by exact prefixLift 8150793
  have htrace : WordTrace (prefixWord ++ tailWord_8150793) baseStart_8150793 baseEnd_8150793 := by
    simpa [prefixWord, tailWord_8150793, baseEnd_8150793] using wordTrace_append hprefix tailTrace_8150793
  have hstable : (prefixWord ++ tailWord_8150793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8150793).length < 2 ^ (prefixWord ++ tailWord_8150793).sum := by decide
  have hdescent : baseEnd_8150793 < baseStart_8150793 := by decide
  rcases family_descends (prefixWord ++ tailWord_8150793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8150794 : List Nat := [3, 1, 2, 2, 1, 4, 2, 2, 1, 3, 2]
def baseStart_8150794 : Nat := 118140960795 + 8150794 * 2 ^ 59
def prefixEnd_8150794 : Nat := 4983230072969 + 3 ^ 40 * 8150794 * 2
def baseEnd_8150794 : Nat := 4185275037782888214690187

theorem tailTrace_8150794 : CollatzResearch.WordTrace tailWord_8150794 prefixEnd_8150794 4185275037782888214690187 := by
  unfold tailWord_8150794
  simp only [CollatzResearch.WordTrace]
  refine ⟨74320970008268214408490859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198189253355381905089308957 74320970008268214408490859)
  ·
    refine ⟨111481455012402321612736289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74320970008268214408490859 111481455012402321612736289)
    ·
      refine ⟨83611091259301741209552217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111481455012402321612736289 83611091259301741209552217)
      ·
        refine ⟨62708318444476305907164163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83611091259301741209552217 62708318444476305907164163)
        ·
          refine ⟨94062477666714458860746245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62708318444476305907164163 94062477666714458860746245)
          ·
            refine ⟨17636714562508961036389921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94062477666714458860746245 17636714562508961036389921)
            ·
              refine ⟨13227535921881720777292441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17636714562508961036389921 13227535921881720777292441)
              ·
                refine ⟨9920651941411290582969331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13227535921881720777292441 9920651941411290582969331)
                ·
                  refine ⟨14880977912116935874453997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9920651941411290582969331 14880977912116935874453997)
                  ·
                    refine ⟨5580366717043850952920249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14880977912116935874453997 5580366717043850952920249)
                    ·
                      refine ⟨4185275037782888214690187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5580366717043850952920249 4185275037782888214690187)
                      ·
                        rfl

theorem cell23_8150794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 2, 1, 3, 2].length) (baseStart_8150794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8150794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8150794 prefixEnd_8150794 := by exact prefixLift 8150794
  have htrace : WordTrace (prefixWord ++ tailWord_8150794) baseStart_8150794 baseEnd_8150794 := by
    simpa [prefixWord, tailWord_8150794, baseEnd_8150794] using wordTrace_append hprefix tailTrace_8150794
  have hstable : (prefixWord ++ tailWord_8150794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8150794).length < 2 ^ (prefixWord ++ tailWord_8150794).sum := by decide
  have hdescent : baseEnd_8150794 < baseStart_8150794 := by decide
  rcases family_descends (prefixWord ++ tailWord_8150794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8150803 : List Nat := [1, 1, 1, 2, 1, 3, 2, 2, 4, 2, 4]
def baseStart_8150803 : Nat := 118140960795 + 8150803 * 2 ^ 59
def prefixEnd_8150803 : Nat := 4983230072969 + 3 ^ 40 * 8150803 * 2
def baseEnd_8150803 : Nat := 4185279659108778679477645

theorem tailTrace_8150803 : CollatzResearch.WordTrace tailWord_8150803 prefixEnd_8150803 4185279659108778679477645 := by
  unfold tailWord_8150803
  simp only [CollatzResearch.WordTrace]
  refine ⟨297284208290040252171041063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198189472193360168114027375 297284208290040252171041063)
  ·
    refine ⟨445926312435060378256561595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297284208290040252171041063 445926312435060378256561595)
    ·
      refine ⟨668889468652590567384842393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445926312435060378256561595 668889468652590567384842393)
      ·
        refine ⟨501667101489442925538631795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 668889468652590567384842393 501667101489442925538631795)
        ·
          refine ⟨752500652234164388307947693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501667101489442925538631795 752500652234164388307947693)
          ·
            refine ⟨282187744587811645615480385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 752500652234164388307947693 282187744587811645615480385)
            ·
              refine ⟨211640808440858734211610289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282187744587811645615480385 211640808440858734211610289)
              ·
                refine ⟨158730606330644050658707717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211640808440858734211610289 158730606330644050658707717)
                ·
                  refine ⟨29761988686995759498507697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158730606330644050658707717 29761988686995759498507697)
                  ·
                    refine ⟨22321491515246819623880773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29761988686995759498507697 22321491515246819623880773)
                    ·
                      refine ⟨4185279659108778679477645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22321491515246819623880773 4185279659108778679477645)
                      ·
                        rfl

theorem cell23_8150803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 2, 4].length) (baseStart_8150803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8150803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8150803 prefixEnd_8150803 := by exact prefixLift 8150803
  have htrace : WordTrace (prefixWord ++ tailWord_8150803) baseStart_8150803 baseEnd_8150803 := by
    simpa [prefixWord, tailWord_8150803, baseEnd_8150803] using wordTrace_append hprefix tailTrace_8150803
  have hstable : (prefixWord ++ tailWord_8150803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8150803).length < 2 ^ (prefixWord ++ tailWord_8150803).sum := by decide
  have hdescent : baseEnd_8150803 < baseStart_8150803 := by decide
  rcases family_descends (prefixWord ++ tailWord_8150803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8150810 : List Nat := [3, 1, 1, 3, 2, 3, 1, 1, 2, 1, 5]
def baseStart_8150810 : Nat := 118140960795 + 8150810 * 2 ^ 59
def prefixEnd_8150810 : Nat := 4983230072969 + 3 ^ 40 * 8150810 * 2
def baseEnd_8150810 : Nat := 4185283253473360152090113

theorem tailTrace_8150810 : CollatzResearch.WordTrace tailWord_8150810 prefixEnd_8150810 4185283253473360152090113 := by
  unfold tailWord_8150810
  simp only [CollatzResearch.WordTrace]
  refine ⟨74321115900253723091636471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198189642400676594911030589 74321115900253723091636471)
  ·
    refine ⟨111481673850380584637454707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74321115900253723091636471 111481673850380584637454707)
    ·
      refine ⟨167222510775570876956182061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111481673850380584637454707 167222510775570876956182061)
      ·
        refine ⟨62708441540839078858568273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167222510775570876956182061 62708441540839078858568273)
        ·
          refine ⟨47031331155629309143926205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62708441540839078858568273 47031331155629309143926205)
          ·
            refine ⟨17636749183360990928972327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47031331155629309143926205 17636749183360990928972327)
            ·
              refine ⟨26455123775041486393458491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17636749183360990928972327 26455123775041486393458491)
              ·
                refine ⟨39682685662562229590187737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26455123775041486393458491 39682685662562229590187737)
                ·
                  refine ⟨29762014246921672192640803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39682685662562229590187737 29762014246921672192640803)
                  ·
                    refine ⟨44643021370382508288961205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29762014246921672192640803 44643021370382508288961205)
                    ·
                      refine ⟨4185283253473360152090113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44643021370382508288961205 4185283253473360152090113)
                      ·
                        rfl

theorem cell23_8150810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_8150810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8150810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8150810 prefixEnd_8150810 := by exact prefixLift 8150810
  have htrace : WordTrace (prefixWord ++ tailWord_8150810) baseStart_8150810 baseEnd_8150810 := by
    simpa [prefixWord, tailWord_8150810, baseEnd_8150810] using wordTrace_append hprefix tailTrace_8150810
  have hstable : (prefixWord ++ tailWord_8150810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8150810).length < 2 ^ (prefixWord ++ tailWord_8150810).sum := by decide
  have hdescent : baseEnd_8150810 < baseStart_8150810 := by decide
  rcases family_descends (prefixWord ++ tailWord_8150810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8150824 : List Nat := [2, 1, 5, 1, 1, 2, 2, 1, 4, 2, 2]
def baseStart_8150824 : Nat := 118140960795 + 8150824 * 2 ^ 59
def prefixEnd_8150824 : Nat := 4983230072969 + 3 ^ 40 * 8150824 * 2
def baseEnd_8150824 : Nat := 4185290442202523097315049

theorem tailTrace_8150824 : CollatzResearch.WordTrace tailWord_8150824 prefixEnd_8150824 4185290442202523097315049 := by
  unfold tailWord_8150824
  simp only [CollatzResearch.WordTrace]
  refine ⟨148642487111482086378777763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198189982815309448505037017 148642487111482086378777763)
  ·
    refine ⟨222963730667223129568166645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148642487111482086378777763 222963730667223129568166645)
    ·
      refine ⟨20902849750052168397015623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 222963730667223129568166645 20902849750052168397015623)
      ·
        refine ⟨31354274625078252595523435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20902849750052168397015623 31354274625078252595523435)
        ·
          refine ⟨47031411937617378893285153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31354274625078252595523435 47031411937617378893285153)
          ·
            refine ⟨35273558953213034169963865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47031411937617378893285153 35273558953213034169963865)
            ·
              refine ⟨26455169214909775627472899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35273558953213034169963865 26455169214909775627472899)
              ·
                refine ⟨39682753822364663441209349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26455169214909775627472899 39682753822364663441209349)
                ·
                  refine ⟨7440516341693374395226753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39682753822364663441209349 7440516341693374395226753)
                  ·
                    refine ⟨5580387256270030796420065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7440516341693374395226753 5580387256270030796420065)
                    ·
                      refine ⟨4185290442202523097315049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5580387256270030796420065 4185290442202523097315049)
                      ·
                        rfl

theorem cell23_8150824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_8150824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8150824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8150824 prefixEnd_8150824 := by exact prefixLift 8150824
  have htrace : WordTrace (prefixWord ++ tailWord_8150824) baseStart_8150824 baseEnd_8150824 := by
    simpa [prefixWord, tailWord_8150824, baseEnd_8150824] using wordTrace_append hprefix tailTrace_8150824
  have hstable : (prefixWord ++ tailWord_8150824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8150824).length < 2 ^ (prefixWord ++ tailWord_8150824).sum := by decide
  have hdescent : baseEnd_8150824 < baseStart_8150824 := by decide
  rcases family_descends (prefixWord ++ tailWord_8150824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8150853 : List Nat := [1, 3, 1, 1, 1, 2, 3, 2, 1, 1, 7]
def baseStart_8150853 : Nat := 118140960795 + 8150853 * 2 ^ 59
def prefixEnd_8150853 : Nat := 4983230072969 + 3 ^ 40 * 8150853 * 2
def baseEnd_8150853 : Nat := 4185305333141503483852415

theorem tailTrace_8150853 : CollatzResearch.WordTrace tailWord_8150853 prefixEnd_8150853 4185305333141503483852415 := by
  unfold tailWord_8150853
  simp only [CollatzResearch.WordTrace]
  refine ⟨297286031939859110710361213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198190687959906073806907475 297286031939859110710361213)
  ·
    refine ⟨111482261977447166516385455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297286031939859110710361213 111482261977447166516385455)
    ·
      refine ⟨167223392966170749774578183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111482261977447166516385455 167223392966170749774578183)
      ·
        refine ⟨250835089449256124661867275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167223392966170749774578183 250835089449256124661867275)
        ·
          refine ⟨376252634173884186992800913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250835089449256124661867275 376252634173884186992800913)
          ·
            refine ⟨282189475630413140244600685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 376252634173884186992800913 282189475630413140244600685)
            ·
              refine ⟨105821053361404927591725257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 282189475630413140244600685 105821053361404927591725257)
              ·
                refine ⟨79365790021053695693793943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105821053361404927591725257 79365790021053695693793943)
                ·
                  refine ⟨119048685031580543540690915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79365790021053695693793943 119048685031580543540690915)
                  ·
                    refine ⟨178573027547370815311036373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 119048685031580543540690915 178573027547370815311036373)
                    ·
                      refine ⟨4185305333141503483852415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 178573027547370815311036373 4185305333141503483852415)
                      ·
                        rfl

theorem cell23_8150853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 1, 7].length) (baseStart_8150853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8150853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8150853 prefixEnd_8150853 := by exact prefixLift 8150853
  have htrace : WordTrace (prefixWord ++ tailWord_8150853) baseStart_8150853 baseEnd_8150853 := by
    simpa [prefixWord, tailWord_8150853, baseEnd_8150853] using wordTrace_append hprefix tailTrace_8150853
  have hstable : (prefixWord ++ tailWord_8150853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8150853).length < 2 ^ (prefixWord ++ tailWord_8150853).sum := by decide
  have hdescent : baseEnd_8150853 < baseStart_8150853 := by decide
  rcases family_descends (prefixWord ++ tailWord_8150853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8150897 : List Nat := [1, 2, 2, 2, 1, 3, 3, 1, 2, 4, 2]
def baseStart_8150897 : Nat := 118140960795 + 8150897 * 2 ^ 59
def prefixEnd_8150897 : Nat := 4983230072969 + 3 ^ 40 * 8150897 * 2
def baseEnd_8150897 : Nat := 4185327926290301311702213

theorem tailTrace_8150897 : CollatzResearch.WordTrace tailWord_8150897 prefixEnd_8150897 4185327926290301311702213 := by
  unfold tailWord_8150897
  simp only [CollatzResearch.WordTrace]
  refine ⟨297287636751699706224962945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198191757834466470816641963 297287636751699706224962945)
  ·
    refine ⟨222965727563774779668722209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297287636751699706224962945 222965727563774779668722209)
    ·
      refine ⟨167224295672831084751541657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222965727563774779668722209 167224295672831084751541657)
      ·
        refine ⟨125418221754623313563656243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167224295672831084751541657 125418221754623313563656243)
        ·
          refine ⟨188127332631934970345484365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125418221754623313563656243 188127332631934970345484365)
          ·
            refine ⟨70547749736975613879556637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188127332631934970345484365 70547749736975613879556637)
            ·
              refine ⟨26455406151365855204833739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70547749736975613879556637 26455406151365855204833739)
              ·
                refine ⟨39683109227048782807250609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26455406151365855204833739 39683109227048782807250609)
                ·
                  refine ⟨29762331920286587105437957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39683109227048782807250609 29762331920286587105437957)
                  ·
                    refine ⟨5580437235053735082269617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29762331920286587105437957 5580437235053735082269617)
                    ·
                      refine ⟨4185327926290301311702213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5580437235053735082269617 4185327926290301311702213)
                      ·
                        rfl

theorem cell23_8150897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 4, 2].length) (baseStart_8150897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8150897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8150897 prefixEnd_8150897 := by exact prefixLift 8150897
  have htrace : WordTrace (prefixWord ++ tailWord_8150897) baseStart_8150897 baseEnd_8150897 := by
    simpa [prefixWord, tailWord_8150897, baseEnd_8150897] using wordTrace_append hprefix tailTrace_8150897
  have hstable : (prefixWord ++ tailWord_8150897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8150897).length < 2 ^ (prefixWord ++ tailWord_8150897).sum := by decide
  have hdescent : baseEnd_8150897 < baseStart_8150897 := by decide
  rcases family_descends (prefixWord ++ tailWord_8150897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8150903 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 12]
def baseStart_8150903 : Nat := 118140960795 + 8150903 * 2 ^ 59
def prefixEnd_8150903 : Nat := 4983230072969 + 3 ^ 40 * 8150903 * 2
def baseEnd_8150903 : Nat := 465036778574914254247465

theorem tailTrace_8150903 : CollatzResearch.WordTrace tailWord_8150903 prefixEnd_8150903 465036778574914254247465 := by
  unfold tailWord_8150903
  simp only [CollatzResearch.WordTrace]
  refine ⟨297287855589677969249681363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198191903726451979499787575 297287855589677969249681363)
  ·
    refine ⟨445931783384516953874522045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297287855589677969249681363 445931783384516953874522045)
    ·
      refine ⟨167224418769193857702945767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 445931783384516953874522045 167224418769193857702945767)
      ·
        refine ⟨250836628153790786554418651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167224418769193857702945767 250836628153790786554418651)
        ·
          refine ⟨376254942230686179831627977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250836628153790786554418651 376254942230686179831627977)
          ·
            refine ⟨282191206673014634873720983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 376254942230686179831627977 282191206673014634873720983)
            ·
              refine ⟨423286810009521952310581475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282191206673014634873720983 423286810009521952310581475)
              ·
                refine ⟨634930215014282928465872213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 423286810009521952310581475 634930215014282928465872213)
                ·
                  refine ⟨465036778574914254247465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 634930215014282928465872213 465036778574914254247465)
                  ·
                    rfl

theorem cell23_8150903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 12].length) (baseStart_8150903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8150903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8150903 prefixEnd_8150903 := by exact prefixLift 8150903
  have htrace : WordTrace (prefixWord ++ tailWord_8150903) baseStart_8150903 baseEnd_8150903 := by
    simpa [prefixWord, tailWord_8150903, baseEnd_8150903] using wordTrace_append hprefix tailTrace_8150903
  have hstable : (prefixWord ++ tailWord_8150903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8150903).length < 2 ^ (prefixWord ++ tailWord_8150903).sum := by decide
  have hdescent : baseEnd_8150903 < baseStart_8150903 := by decide
  rcases family_descends (prefixWord ++ tailWord_8150903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8150974 : List Nat := [4, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2]
def baseStart_8150974 : Nat := 118140960795 + 8150974 * 2 ^ 59
def prefixEnd_8150974 : Nat := 4983230072969 + 3 ^ 40 * 8150974 * 2
def baseEnd_8150974 : Nat := 4185367464300697510439359

theorem tailTrace_8150974 : CollatzResearch.WordTrace tailWord_8150974 prefixEnd_8150974 4185367464300697510439359 := by
  unfold tailWord_8150974
  simp only [CollatzResearch.WordTrace]
  refine ⟨37161305646552593546939497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198193630114947165583677317 37161305646552593546939497)
  ·
    refine ⟨27870979234914445160204623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37161305646552593546939497 27870979234914445160204623)
    ·
      refine ⟨41806468852371667740306935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27870979234914445160204623 41806468852371667740306935)
      ·
        refine ⟨62709703278557501610460403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41806468852371667740306935 62709703278557501610460403)
        ·
          refine ⟨94064554917836252415690605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62709703278557501610460403 94064554917836252415690605)
          ·
            refine ⟨35274208094188594655883977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94064554917836252415690605 35274208094188594655883977)
            ·
              refine ⟨26455656070641445991912983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35274208094188594655883977 26455656070641445991912983)
              ·
                refine ⟨39683484105962168987869475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26455656070641445991912983 39683484105962168987869475)
                ·
                  refine ⟨59525226158943253481804213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39683484105962168987869475 59525226158943253481804213)
                  ·
                    refine ⟨5580489952400930013919145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59525226158943253481804213 5580489952400930013919145)
                    ·
                      refine ⟨4185367464300697510439359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5580489952400930013919145 4185367464300697510439359)
                      ·
                        rfl

theorem cell23_8150974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2].length) (baseStart_8150974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8150974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8150974 prefixEnd_8150974 := by exact prefixLift 8150974
  have htrace : WordTrace (prefixWord ++ tailWord_8150974) baseStart_8150974 baseEnd_8150974 := by
    simpa [prefixWord, tailWord_8150974, baseEnd_8150974] using wordTrace_append hprefix tailTrace_8150974
  have hstable : (prefixWord ++ tailWord_8150974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8150974).length < 2 ^ (prefixWord ++ tailWord_8150974).sum := by decide
  have hdescent : baseEnd_8150974 < baseStart_8150974 := by decide
  rcases family_descends (prefixWord ++ tailWord_8150974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8150987 : List Nat := [1, 1, 1, 1, 3, 4, 1, 5, 1, 1, 4]
def baseStart_8150987 : Nat := 118140960795 + 8150987 * 2 ^ 59
def prefixEnd_8150987 : Nat := 4983230072969 + 3 ^ 40 * 8150987 * 2
def baseEnd_8150987 : Nat := 4185374139549205959576799

theorem tailTrace_8150987 : CollatzResearch.WordTrace tailWord_8150987 prefixEnd_8150987 4185374139549205959576799 := by
  unfold tailWord_8150987
  simp only [CollatzResearch.WordTrace]
  refine ⟨297290919321373651595739215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198193946214249101063826143 297290919321373651595739215)
  ·
    refine ⟨445936378982060477393608823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297290919321373651595739215 445936378982060477393608823)
    ·
      refine ⟨668904568473090716090413235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445936378982060477393608823 668904568473090716090413235)
      ·
        refine ⟨1003356852709636074135619853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 668904568473090716090413235 1003356852709636074135619853)
        ·
          refine ⟨376258819766113527800857445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1003356852709636074135619853 376258819766113527800857445)
          ·
            refine ⟨70548528706146286462660771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 376258819766113527800857445 70548528706146286462660771)
            ·
              refine ⟨105822793059219429693991157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70548528706146286462660771 105822793059219429693991157)
              ·
                refine ⟨9920886849301821533811671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105822793059219429693991157 9920886849301821533811671)
                ·
                  refine ⟨14881330273952732300717507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9920886849301821533811671 14881330273952732300717507)
                  ·
                    refine ⟨22321995410929098451076261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14881330273952732300717507 22321995410929098451076261)
                    ·
                      refine ⟨4185374139549205959576799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22321995410929098451076261 4185374139549205959576799)
                      ·
                        rfl

theorem cell23_8150987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 5, 1, 1, 4].length) (baseStart_8150987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8150987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8150987 prefixEnd_8150987 := by exact prefixLift 8150987
  have htrace : WordTrace (prefixWord ++ tailWord_8150987) baseStart_8150987 baseEnd_8150987 := by
    simpa [prefixWord, tailWord_8150987, baseEnd_8150987] using wordTrace_append hprefix tailTrace_8150987
  have hstable : (prefixWord ++ tailWord_8150987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8150987).length < 2 ^ (prefixWord ++ tailWord_8150987).sum := by decide
  have hdescent : baseEnd_8150987 < baseStart_8150987 := by decide
  rcases family_descends (prefixWord ++ tailWord_8150987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151000 : List Nat := [2, 1, 2, 2, 2, 2, 1, 1, 3, 1, 6]
def baseStart_8151000 : Nat := 118140960795 + 8151000 * 2 ^ 59
def prefixEnd_8151000 : Nat := 4983230072969 + 3 ^ 40 * 8151000 * 2
def baseEnd_8151000 : Nat := 4185380814797714408714239

theorem tailTrace_8151000 : CollatzResearch.WordTrace tailWord_8151000 prefixEnd_8151000 4185380814797714408714239 := by
  unfold tailWord_8151000
  simp only [CollatzResearch.WordTrace]
  refine ⟨148645696735163277407981227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198194262313551036543974969 148645696735163277407981227)
  ·
    refine ⟨222968545102744916111971841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148645696735163277407981227 222968545102744916111971841)
    ·
      refine ⟨167226408827058687083978881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222968545102744916111971841 167226408827058687083978881)
      ·
        refine ⟨125419806620294015312984161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167226408827058687083978881 125419806620294015312984161)
        ·
          refine ⟨94064854965220511484738121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125419806620294015312984161 94064854965220511484738121)
          ·
            refine ⟨70548641223915383613553591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94064854965220511484738121 70548641223915383613553591)
            ·
              refine ⟨105822961835873075420330387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70548641223915383613553591 105822961835873075420330387)
              ·
                refine ⟨158734442753809613130495581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105822961835873075420330387 158734442753809613130495581)
                ·
                  refine ⟨59525416032678604923935843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158734442753809613130495581 59525416032678604923935843)
                  ·
                    refine ⟨89288124049017907385903765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59525416032678604923935843 89288124049017907385903765)
                    ·
                      refine ⟨4185380814797714408714239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89288124049017907385903765 4185380814797714408714239)
                      ·
                        rfl

theorem cell23_8151000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_8151000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151000 prefixEnd_8151000 := by exact prefixLift 8151000
  have htrace : WordTrace (prefixWord ++ tailWord_8151000) baseStart_8151000 baseEnd_8151000 := by
    simpa [prefixWord, tailWord_8151000, baseEnd_8151000] using wordTrace_append hprefix tailTrace_8151000
  have hstable : (prefixWord ++ tailWord_8151000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151000).length < 2 ^ (prefixWord ++ tailWord_8151000).sum := by decide
  have hdescent : baseEnd_8151000 < baseStart_8151000 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151007 : List Nat := [1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 5]
def baseStart_8151007 : Nat := 118140960795 + 8151007 * 2 ^ 59
def prefixEnd_8151007 : Nat := 4983230072969 + 3 ^ 40 * 8151007 * 2
def baseEnd_8151007 : Nat := 4185384409162295881326707

theorem tailTrace_8151007 : CollatzResearch.WordTrace tailWord_8151007 prefixEnd_8151007 4185384409162295881326707 := by
  unfold tailWord_8151007
  simp only [CollatzResearch.WordTrace]
  refine ⟨297291648781301195011467275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198194432520867463340978183 297291648781301195011467275)
  ·
    refine ⟨445937473171951792517200913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297291648781301195011467275 445937473171951792517200913)
    ·
      refine ⟨334453104878963844387900685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445937473171951792517200913 334453104878963844387900685)
      ·
        refine ⟨125419914329611441645462757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334453104878963844387900685 125419914329611441645462757)
        ·
          refine ⟨23516233936802145308524267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125419914329611441645462757 23516233936802145308524267)
          ·
            refine ⟨35274350905203217962786401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23516233936802145308524267 35274350905203217962786401)
            ·
              refine ⟨26455763178902413472089801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35274350905203217962786401 26455763178902413472089801)
              ·
                refine ⟨19841822384176810104067351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26455763178902413472089801 19841822384176810104067351)
                ·
                  refine ⟨29762733576265215156101027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19841822384176810104067351 29762733576265215156101027)
                  ·
                    refine ⟨44644100364397822734151541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29762733576265215156101027 44644100364397822734151541)
                    ·
                      refine ⟨4185384409162295881326707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44644100364397822734151541 4185384409162295881326707)
                      ·
                        rfl

theorem cell23_8151007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_8151007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151007 prefixEnd_8151007 := by exact prefixLift 8151007
  have htrace : WordTrace (prefixWord ++ tailWord_8151007) baseStart_8151007 baseEnd_8151007 := by
    simpa [prefixWord, tailWord_8151007, baseEnd_8151007] using wordTrace_append hprefix tailTrace_8151007
  have hstable : (prefixWord ++ tailWord_8151007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151007).length < 2 ^ (prefixWord ++ tailWord_8151007).sum := by decide
  have hdescent : baseEnd_8151007 < baseStart_8151007 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151021 : List Nat := [1, 5, 1, 4, 1, 1, 1, 1, 3, 1, 4]
def baseStart_8151021 : Nat := 118140960795 + 8151021 * 2 ^ 59
def prefixEnd_8151021 : Nat := 4983230072969 + 3 ^ 40 * 8151021 * 2
def baseEnd_8151021 : Nat := 4185391597891458826551643

theorem tailTrace_8151021 : CollatzResearch.WordTrace tailWord_8151021 prefixEnd_8151021 4185391597891458826551643 := by
  unfold tailWord_8151021
  simp only [CollatzResearch.WordTrace]
  refine ⟨297292159403250475402476917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198194772935500316934984611 297292159403250475402476917)
  ·
    refine ⟨27871139944054732068982211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 297292159403250475402476917 27871139944054732068982211)
    ·
      refine ⟨41806709916082098103473317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27871139944054732068982211 41806709916082098103473317)
      ·
        refine ⟨7838758109265393394401247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41806709916082098103473317 7838758109265393394401247)
        ·
          refine ⟨11758137163898090091601871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7838758109265393394401247 11758137163898090091601871)
          ·
            refine ⟨17637205745847135137402807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11758137163898090091601871 17637205745847135137402807)
            ·
              refine ⟨26455808618770702706104211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17637205745847135137402807 26455808618770702706104211)
              ·
                refine ⟨39683712928156054059156317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26455808618770702706104211 39683712928156054059156317)
                ·
                  refine ⟨14881392348058520272183619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39683712928156054059156317 14881392348058520272183619)
                  ·
                    refine ⟨22322088522087780408275429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14881392348058520272183619 22322088522087780408275429)
                    ·
                      refine ⟨4185391597891458826551643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22322088522087780408275429 4185391597891458826551643)
                      ·
                        rfl

theorem cell23_8151021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_8151021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151021 prefixEnd_8151021 := by exact prefixLift 8151021
  have htrace : WordTrace (prefixWord ++ tailWord_8151021) baseStart_8151021 baseEnd_8151021 := by
    simpa [prefixWord, tailWord_8151021, baseEnd_8151021] using wordTrace_append hprefix tailTrace_8151021
  have hstable : (prefixWord ++ tailWord_8151021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151021).length < 2 ^ (prefixWord ++ tailWord_8151021).sum := by decide
  have hdescent : baseEnd_8151021 < baseStart_8151021 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151024 : List Nat := [2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 3]
def baseStart_8151024 : Nat := 118140960795 + 8151024 * 2 ^ 59
def prefixEnd_8151024 : Nat := 4983230072969 + 3 ^ 40 * 8151024 * 2
def baseEnd_8151024 : Nat := 4185393138333422314814129

theorem tailTrace_8151024 : CollatzResearch.WordTrace tailWord_8151024 prefixEnd_8151024 4185393138333422314814129 := by
  unfold tailWord_8151024
  simp only [CollatzResearch.WordTrace]
  refine ⟨148646134411119803457418063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198194845881493071276557417 148646134411119803457418063)
  ·
    refine ⟨222969201616679705186127095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148646134411119803457418063 222969201616679705186127095)
    ·
      refine ⟨334453802425019557779190643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222969201616679705186127095 334453802425019557779190643)
      ·
        refine ⟨501680703637529336668785965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334453802425019557779190643 501680703637529336668785965)
        ·
          refine ⟨188130263864073501250794737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 501680703637529336668785965 188130263864073501250794737)
          ·
            refine ⟨141097697898055125938096053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188130263864073501250794737 141097697898055125938096053)
            ·
              refine ⟨13227909177942668056696505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141097697898055125938096053 13227909177942668056696505)
              ·
                refine ⟨9920931883457001042522379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13227909177942668056696505 9920931883457001042522379)
                ·
                  refine ⟨14881397825185501563783569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9920931883457001042522379 14881397825185501563783569)
                  ·
                    refine ⟨11161048368889126172837677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14881397825185501563783569 11161048368889126172837677)
                    ·
                      refine ⟨4185393138333422314814129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11161048368889126172837677 4185393138333422314814129)
                      ·
                        rfl

theorem cell23_8151024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 3].length) (baseStart_8151024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151024 prefixEnd_8151024 := by exact prefixLift 8151024
  have htrace : WordTrace (prefixWord ++ tailWord_8151024) baseStart_8151024 baseEnd_8151024 := by
    simpa [prefixWord, tailWord_8151024, baseEnd_8151024] using wordTrace_append hprefix tailTrace_8151024
  have hstable : (prefixWord ++ tailWord_8151024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151024).length < 2 ^ (prefixWord ++ tailWord_8151024).sum := by decide
  have hdescent : baseEnd_8151024 < baseStart_8151024 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151037 : List Nat := [1, 4, 1, 1, 1, 2, 3, 1, 3, 3, 3]
def baseStart_8151037 : Nat := 118140960795 + 8151037 * 2 ^ 59
def prefixEnd_8151037 : Nat := 4983230072969 + 3 ^ 40 * 8151037 * 2
def baseEnd_8151037 : Nat := 4185399813581930763951569

theorem tailTrace_8151037 : CollatzResearch.WordTrace tailWord_8151037 prefixEnd_8151037 4185399813581930763951569 := by
  unfold tailWord_8151037
  simp only [CollatzResearch.WordTrace]
  refine ⟨297292742971192510135059365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198195161980795006756706243 297292742971192510135059365)
  ·
    refine ⟨55742389307098595650323631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 297292742971192510135059365 55742389307098595650323631)
    ·
      refine ⟨83613583960647893475485447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55742389307098595650323631 83613583960647893475485447)
      ·
        refine ⟨125420375940971840213228171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83613583960647893475485447 125420375940971840213228171)
        ·
          refine ⟨188130563911457760319842257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125420375940971840213228171 188130563911457760319842257)
          ·
            refine ⟨141097922933593320239881693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188130563911457760319842257 141097922933593320239881693)
            ·
              refine ⟨52911721100097495089955635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141097922933593320239881693 52911721100097495089955635)
              ·
                refine ⟨79367581650146242634933453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52911721100097495089955635 79367581650146242634933453)
                ·
                  refine ⟨29762843118804840988100045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79367581650146242634933453 29762843118804840988100045)
                  ·
                    refine ⟨11161066169551815370537517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29762843118804840988100045 11161066169551815370537517)
                    ·
                      refine ⟨4185399813581930763951569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11161066169551815370537517 4185399813581930763951569)
                      ·
                        rfl

theorem cell23_8151037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 3, 3].length) (baseStart_8151037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151037 prefixEnd_8151037 := by exact prefixLift 8151037
  have htrace : WordTrace (prefixWord ++ tailWord_8151037) baseStart_8151037 baseEnd_8151037 := by
    simpa [prefixWord, tailWord_8151037, baseEnd_8151037] using wordTrace_append hprefix tailTrace_8151037
  have hstable : (prefixWord ++ tailWord_8151037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151037).length < 2 ^ (prefixWord ++ tailWord_8151037).sum := by decide
  have hdescent : baseEnd_8151037 < baseStart_8151037 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151038 : List Nat := [4, 2, 2, 2, 1, 2, 3, 1, 1, 1, 4]
def baseStart_8151038 : Nat := 118140960795 + 8151038 * 2 ^ 59
def prefixEnd_8151038 : Nat := 4983230072969 + 3 ^ 40 * 8151038 * 2
def baseEnd_8151038 : Nat := 4185400327062585260039065

theorem tailTrace_8151038 : CollatzResearch.WordTrace tailWord_8151038 prefixEnd_8151038 4185400327062585260039065 := by
  unfold tailWord_8151038
  simp only [CollatzResearch.WordTrace]
  refine ⟨37161597430523610913230721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198195186296125924870563845 37161597430523610913230721)
  ·
    refine ⟨27871198072892708184923041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37161597430523610913230721 27871198072892708184923041)
    ·
      refine ⟨20903398554669531138692281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27871198072892708184923041 20903398554669531138692281)
      ·
        refine ⟨15677548916002148354019211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20903398554669531138692281 15677548916002148354019211)
        ·
          refine ⟨23516323374003222531028817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15677548916002148354019211 23516323374003222531028817)
          ·
            refine ⟨17637242530502416898271613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23516323374003222531028817 17637242530502416898271613)
            ·
              refine ⟨6613965948938406336851855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17637242530502416898271613 6613965948938406336851855)
              ·
                refine ⟨9920948923407609505277783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6613965948938406336851855 9920948923407609505277783)
                ·
                  refine ⟨14881423385111414257916675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9920948923407609505277783 14881423385111414257916675)
                  ·
                    refine ⟨22322135077667121386875013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14881423385111414257916675 22322135077667121386875013)
                    ·
                      refine ⟨4185400327062585260039065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22322135077667121386875013 4185400327062585260039065)
                      ·
                        rfl

theorem cell23_8151038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_8151038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151038 prefixEnd_8151038 := by exact prefixLift 8151038
  have htrace : WordTrace (prefixWord ++ tailWord_8151038) baseStart_8151038 baseEnd_8151038 := by
    simpa [prefixWord, tailWord_8151038, baseEnd_8151038] using wordTrace_append hprefix tailTrace_8151038
  have hstable : (prefixWord ++ tailWord_8151038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151038).length < 2 ^ (prefixWord ++ tailWord_8151038).sum := by decide
  have hdescent : baseEnd_8151038 < baseStart_8151038 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151041 : List Nat := [1, 2, 4, 1, 2, 1, 5, 1, 1, 2, 3]
def baseStart_8151041 : Nat := 118140960795 + 8151041 * 2 ^ 59
def prefixEnd_8151041 : Nat := 4983230072969 + 3 ^ 40 * 8151041 * 2
def baseEnd_8151041 : Nat := 4185401867504548748301551

theorem tailTrace_8151041 : CollatzResearch.WordTrace tailWord_8151041 prefixEnd_8151041 4185401867504548748301551 := by
  unfold tailWord_8151041
  simp only [CollatzResearch.WordTrace]
  refine ⟨297292888863178018818204977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198195259242118679212136651 297292888863178018818204977)
  ·
    refine ⟨222969666647383514113653733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297292888863178018818204977 222969666647383514113653733)
    ·
      refine ⟨41806812496384408896310075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222969666647383514113653733 41806812496384408896310075)
      ·
        refine ⟨62710218744576613344465113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41806812496384408896310075 62710218744576613344465113)
        ·
          refine ⟨47032664058432460008348835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62710218744576613344465113 47032664058432460008348835)
          ·
            refine ⟨70548996087648690012523253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47032664058432460008348835 70548996087648690012523253)
            ·
              refine ⟨6613968383217064688674055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70548996087648690012523253 6613968383217064688674055)
              ·
                refine ⟨9920952574825597033011083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6613968383217064688674055 9920952574825597033011083)
                ·
                  refine ⟨14881428862238395549516625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9920952574825597033011083 14881428862238395549516625)
                  ·
                    refine ⟨11161071646678796662137469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14881428862238395549516625 11161071646678796662137469)
                    ·
                      refine ⟨4185401867504548748301551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11161071646678796662137469 4185401867504548748301551)
                      ·
                        rfl

theorem cell23_8151041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 1, 1, 2, 3].length) (baseStart_8151041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151041 prefixEnd_8151041 := by exact prefixLift 8151041
  have htrace : WordTrace (prefixWord ++ tailWord_8151041) baseStart_8151041 baseEnd_8151041 := by
    simpa [prefixWord, tailWord_8151041, baseEnd_8151041] using wordTrace_append hprefix tailTrace_8151041
  have hstable : (prefixWord ++ tailWord_8151041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151041).length < 2 ^ (prefixWord ++ tailWord_8151041).sum := by decide
  have hdescent : baseEnd_8151041 < baseStart_8151041 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151044 : List Nat := [2, 3, 2, 4, 2, 10]
def baseStart_8151044 : Nat := 118140960795 + 8151044 * 2 ^ 59
def prefixEnd_8151044 : Nat := 4983230072969 + 3 ^ 40 * 8151044 * 2
def baseEnd_8151044 : Nat := 17223882337228445417959

theorem tailTrace_8151044 : CollatzResearch.WordTrace tailWord_8151044 prefixEnd_8151044 17223882337228445417959 := by
  unfold tailWord_8151044
  simp only [CollatzResearch.WordTrace]
  refine ⟨148646499141083575165282093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198195332188111433553709457 148646499141083575165282093)
  ·
    refine ⟨55742437177906340686980785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148646499141083575165282093 55742437177906340686980785)
    ·
      refine ⟨41806827883429755515235589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55742437177906340686980785 41806827883429755515235589)
      ·
        refine ⟨7838780228143079159106673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41806827883429755515235589 7838780228143079159106673)
        ·
          refine ⟨5879085171107309369330005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7838780228143079159106673 5879085171107309369330005)
          ·
            refine ⟨17223882337228445417959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5879085171107309369330005 17223882337228445417959)
            ·
              rfl

theorem cell23_8151044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 10].length) (baseStart_8151044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151044 prefixEnd_8151044 := by exact prefixLift 8151044
  have htrace : WordTrace (prefixWord ++ tailWord_8151044) baseStart_8151044 baseEnd_8151044 := by
    simpa [prefixWord, tailWord_8151044, baseEnd_8151044] using wordTrace_append hprefix tailTrace_8151044
  have hstable : (prefixWord ++ tailWord_8151044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151044).length < 2 ^ (prefixWord ++ tailWord_8151044).sum := by decide
  have hdescent : baseEnd_8151044 < baseStart_8151044 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151064 : List Nat := [2, 1, 2, 3, 2, 1, 1, 1, 5, 3, 2]
def baseStart_8151064 : Nat := 118140960795 + 8151064 * 2 ^ 59
def prefixEnd_8151064 : Nat := 4983230072969 + 3 ^ 40 * 8151064 * 2
def baseEnd_8151064 : Nat := 4185413677559602158313945

theorem tailTrace_8151064 : CollatzResearch.WordTrace tailWord_8151064 prefixEnd_8151064 4185413677559602158313945 := by
  unfold tailWord_8151064
  simp only [CollatzResearch.WordTrace]
  refine ⟨148646863871047346873146123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198195818494729795830861497 148646863871047346873146123)
  ·
    refine ⟨222970295806571020309719185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148646863871047346873146123 222970295806571020309719185)
    ·
      refine ⟨167227721854928265232289389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222970295806571020309719185 167227721854928265232289389)
      ·
        refine ⟨62710395695598099462108521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167227721854928265232289389 62710395695598099462108521)
        ·
          refine ⟨47032796771698574596581391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62710395695598099462108521 47032796771698574596581391)
          ·
            refine ⟨70549195157547861894872087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47032796771698574596581391 70549195157547861894872087)
            ·
              refine ⟨105823792736321792842308131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70549195157547861894872087 105823792736321792842308131)
              ·
                refine ⟨158735689104482689263462197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105823792736321792842308131 158735689104482689263462197)
                ·
                  refine ⟨14881470853545252118449581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 158735689104482689263462197 14881470853545252118449581)
                  ·
                    refine ⟨5580551570079469544418593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14881470853545252118449581 5580551570079469544418593)
                    ·
                      refine ⟨4185413677559602158313945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5580551570079469544418593 4185413677559602158313945)
                      ·
                        rfl

theorem cell23_8151064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 5, 3, 2].length) (baseStart_8151064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151064 prefixEnd_8151064 := by exact prefixLift 8151064
  have htrace : WordTrace (prefixWord ++ tailWord_8151064) baseStart_8151064 baseEnd_8151064 := by
    simpa [prefixWord, tailWord_8151064, baseEnd_8151064] using wordTrace_append hprefix tailTrace_8151064
  have hstable : (prefixWord ++ tailWord_8151064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151064).length < 2 ^ (prefixWord ++ tailWord_8151064).sum := by decide
  have hdescent : baseEnd_8151064 < baseStart_8151064 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151092 : List Nat := [2, 5, 1, 2, 3, 1, 2, 1, 1, 2, 3]
def baseStart_8151092 : Nat := 118140960795 + 8151092 * 2 ^ 59
def prefixEnd_8151092 : Nat := 4983230072969 + 3 ^ 40 * 8151092 * 2
def baseEnd_8151092 : Nat := 4185428055017928048763817

theorem tailTrace_8151092 : CollatzResearch.WordTrace tailWord_8151092 prefixEnd_8151092 4185428055017928048763817 := by
  unfold tailWord_8151092
  simp only [CollatzResearch.WordTrace]
  refine ⟨148647374492996627264155765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198196499323995503018874353 148647374492996627264155765)
  ·
    refine ⟨13935691358718433806014603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148647374492996627264155765 13935691358718433806014603)
    ·
      refine ⟨20903537038077650709021905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13935691358718433806014603 20903537038077650709021905)
      ·
        refine ⟨15677652778558238031766429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20903537038077650709021905 15677652778558238031766429)
        ·
          refine ⟨5879119791959339261912411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15677652778558238031766429 5879119791959339261912411)
          ·
            refine ⟨8818679687939008892868617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5879119791959339261912411 8818679687939008892868617)
            ·
              refine ⟨6614009765954256669651463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8818679687939008892868617 6614009765954256669651463)
              ·
                refine ⟨9921014648931385004477195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6614009765954256669651463 9921014648931385004477195)
                ·
                  refine ⟨14881521973397077506715793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9921014648931385004477195 14881521973397077506715793)
                  ·
                    refine ⟨11161141480047808130036845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14881521973397077506715793 11161141480047808130036845)
                    ·
                      refine ⟨4185428055017928048763817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11161141480047808130036845 4185428055017928048763817)
                      ·
                        rfl

theorem cell23_8151092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_8151092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151092 prefixEnd_8151092 := by exact prefixLift 8151092
  have htrace : WordTrace (prefixWord ++ tailWord_8151092) baseStart_8151092 baseEnd_8151092 := by
    simpa [prefixWord, tailWord_8151092, baseEnd_8151092] using wordTrace_append hprefix tailTrace_8151092
  have hstable : (prefixWord ++ tailWord_8151092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151092).length < 2 ^ (prefixWord ++ tailWord_8151092).sum := by decide
  have hdescent : baseEnd_8151092 < baseStart_8151092 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151111 : List Nat := [1, 1, 4, 1, 3, 1, 3, 1, 4, 2, 2]
def baseStart_8151111 : Nat := 118140960795 + 8151111 * 2 ^ 59
def prefixEnd_8151111 : Nat := 4983230072969 + 3 ^ 40 * 8151111 * 2
def baseEnd_8151111 : Nat := 4185437811150363474426229

theorem tailTrace_8151111 : CollatzResearch.WordTrace tailWord_8151111 prefixEnd_8151111 4185437811150363474426229 := by
  unfold tailWord_8151111
  simp only [CollatzResearch.WordTrace]
  refine ⟨297295441972924420773253187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198196961315282947182168791 297295441972924420773253187)
  ·
    refine ⟨445943162959386631159879781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297295441972924420773253187 445943162959386631159879781)
    ·
      refine ⟨83614343054884993342477459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 445943162959386631159879781 83614343054884993342477459)
      ·
        refine ⟨125421514582327490013716189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83614343054884993342477459 125421514582327490013716189)
        ·
          refine ⟨47033067968372808755143571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125421514582327490013716189 47033067968372808755143571)
          ·
            refine ⟨70549601952559213132715357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47033067968372808755143571 70549601952559213132715357)
            ·
              refine ⟨26456100732209704924768259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70549601952559213132715357 26456100732209704924768259)
              ·
                refine ⟨39684151098314557387152389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26456100732209704924768259 39684151098314557387152389)
                ·
                  refine ⟨7440778330933979510091073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39684151098314557387152389 7440778330933979510091073)
                  ·
                    refine ⟨5580583748200484632568305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7440778330933979510091073 5580583748200484632568305)
                    ·
                      refine ⟨4185437811150363474426229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5580583748200484632568305 4185437811150363474426229)
                      ·
                        rfl

theorem cell23_8151111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 4, 2, 2].length) (baseStart_8151111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151111 prefixEnd_8151111 := by exact prefixLift 8151111
  have htrace : WordTrace (prefixWord ++ tailWord_8151111) baseStart_8151111 baseEnd_8151111 := by
    simpa [prefixWord, tailWord_8151111, baseEnd_8151111] using wordTrace_append hprefix tailTrace_8151111
  have hstable : (prefixWord ++ tailWord_8151111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151111).length < 2 ^ (prefixWord ++ tailWord_8151111).sum := by decide
  have hdescent : baseEnd_8151111 < baseStart_8151111 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151151 : List Nat := [1, 1, 2, 1, 3, 6, 1, 3, 5]
def baseStart_8151151 : Nat := 118140960795 + 8151151 * 2 ^ 59
def prefixEnd_8151151 : Nat := 4983230072969 + 3 ^ 40 * 8151151 * 2
def baseEnd_8151151 : Nat := 465050927819615924214005

theorem tailTrace_8151151 : CollatzResearch.WordTrace tailWord_8151151 prefixEnd_8151151 465050927819615924214005 := by
  unfold tailWord_8151151
  simp only [CollatzResearch.WordTrace]
  refine ⟨297296900892779507604709307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198197933928519671736472871 297296900892779507604709307)
  ·
    refine ⟨445945351339169261407063961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297296900892779507604709307 445945351339169261407063961)
    ·
      refine ⟨334459013504376946055297971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445945351339169261407063961 334459013504376946055297971)
      ·
        refine ⟨501688520256565419082946957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334459013504376946055297971 501688520256565419082946957)
        ·
          refine ⟨188133195096212032156105109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 501688520256565419082946957 188133195096212032156105109)
          ·
            refine ⟨8818743520134939007317427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 188133195096212032156105109 8818743520134939007317427)
            ·
              refine ⟨13228115280202408510976141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8818743520134939007317427 13228115280202408510976141)
              ·
                refine ⟨4960543230075903191616053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13228115280202408510976141 4960543230075903191616053)
                ·
                  refine ⟨465050927819615924214005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4960543230075903191616053 465050927819615924214005)
                  ·
                    rfl

theorem cell23_8151151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 3, 5].length) (baseStart_8151151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151151 prefixEnd_8151151 := by exact prefixLift 8151151
  have htrace : WordTrace (prefixWord ++ tailWord_8151151) baseStart_8151151 baseEnd_8151151 := by
    simpa [prefixWord, tailWord_8151151, baseEnd_8151151] using wordTrace_append hprefix tailTrace_8151151
  have hstable : (prefixWord ++ tailWord_8151151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151151).length < 2 ^ (prefixWord ++ tailWord_8151151).sum := by decide
  have hdescent : baseEnd_8151151 < baseStart_8151151 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151164 : List Nat := [2, 2, 2, 1, 1, 5, 1, 2, 2, 5]
def baseStart_8151164 : Nat := 118140960795 + 8151164 * 2 ^ 59
def prefixEnd_8151164 : Nat := 4983230072969 + 3 ^ 40 * 8151164 * 2
def baseEnd_8151164 : Nat := 1395155008541683922354495

theorem tailTrace_8151164 : CollatzResearch.WordTrace tailWord_8151164 prefixEnd_8151164 1395155008541683922354495 := by
  unfold tailWord_8151164
  simp only [CollatzResearch.WordTrace]
  refine ⟨148648687520866205412466273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198198250027821607216621697 148648687520866205412466273)
  ·
    refine ⟨111486515640649654059349705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148648687520866205412466273 111486515640649654059349705)
    ·
      refine ⟨83614886730487240544512279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111486515640649654059349705 83614886730487240544512279)
      ·
        refine ⟨125422330095730860816768419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83614886730487240544512279 125422330095730860816768419)
        ·
          refine ⟨188133495143596291225152629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125422330095730860816768419 188133495143596291225152629)
          ·
            refine ⟨17637515169712152302358059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 188133495143596291225152629 17637515169712152302358059)
            ·
              refine ⟨26456272754568228453537089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17637515169712152302358059 26456272754568228453537089)
              ·
                refine ⟨19842204565926171340152817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26456272754568228453537089 19842204565926171340152817)
                ·
                  refine ⟨14881653424444628505114613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19842204565926171340152817 14881653424444628505114613)
                  ·
                    refine ⟨1395155008541683922354495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14881653424444628505114613 1395155008541683922354495)
                    ·
                      rfl

theorem cell23_8151164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 2, 5].length) (baseStart_8151164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151164 prefixEnd_8151164 := by exact prefixLift 8151164
  have htrace : WordTrace (prefixWord ++ tailWord_8151164) baseStart_8151164 baseEnd_8151164 := by
    simpa [prefixWord, tailWord_8151164, baseEnd_8151164] using wordTrace_append hprefix tailTrace_8151164
  have hstable : (prefixWord ++ tailWord_8151164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151164).length < 2 ^ (prefixWord ++ tailWord_8151164).sum := by decide
  have hdescent : baseEnd_8151164 < baseStart_8151164 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151184 : List Nat := [2, 1, 1, 1, 1, 1, 6, 1, 1, 6, 2]
def baseStart_8151184 : Nat := 118140960795 + 8151184 * 2 ^ 59
def prefixEnd_8151184 : Nat := 4983230072969 + 3 ^ 40 * 8151184 * 2
def baseEnd_8151184 : Nat := 4185475295238141688813393

theorem tailTrace_8151184 : CollatzResearch.WordTrace tailWord_8151184 prefixEnd_8151184 4185475295238141688813393 := by
  unfold tailWord_8151184
  simp only [CollatzResearch.WordTrace]
  refine ⟨148649052250829977120330303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198198736334439969493773737 148649052250829977120330303)
  ·
    refine ⟨222973578376244965680495455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148649052250829977120330303 222973578376244965680495455)
    ·
      refine ⟨334460367564367448520743183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222973578376244965680495455 334460367564367448520743183)
      ·
        refine ⟨501690551346551172781114775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334460367564367448520743183 501690551346551172781114775)
        ·
          refine ⟨752535827019826759171672163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501690551346551172781114775 752535827019826759171672163)
          ·
            refine ⟨1128803740529740138757508245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 752535827019826759171672163 1128803740529740138757508245)
            ·
              refine ⟨52912675337331569004258199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1128803740529740138757508245 52912675337331569004258199)
              ·
                refine ⟨79369013005997353506387299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52912675337331569004258199 79369013005997353506387299)
                ·
                  refine ⟨119053519508996030259580949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79369013005997353506387299 119053519508996030259580949)
                  ·
                    refine ⟨5580633726984188918417857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 119053519508996030259580949 5580633726984188918417857)
                    ·
                      refine ⟨4185475295238141688813393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5580633726984188918417857 4185475295238141688813393)
                      ·
                        rfl

theorem cell23_8151184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 1, 6, 2].length) (baseStart_8151184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151184 prefixEnd_8151184 := by exact prefixLift 8151184
  have htrace : WordTrace (prefixWord ++ tailWord_8151184) baseStart_8151184 baseEnd_8151184 := by
    simpa [prefixWord, tailWord_8151184, baseEnd_8151184] using wordTrace_append hprefix tailTrace_8151184
  have hstable : (prefixWord ++ tailWord_8151184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151184).length < 2 ^ (prefixWord ++ tailWord_8151184).sum := by decide
  have hdescent : baseEnd_8151184 < baseStart_8151184 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151198 : List Nat := [4, 3, 1, 1, 3, 1, 2, 1, 2, 5]
def baseStart_8151198 : Nat := 118140960795 + 8151198 * 2 ^ 59
def prefixEnd_8151198 : Nat := 4983230072969 + 3 ^ 40 * 8151198 * 2
def baseEnd_8151198 : Nat := 1395160827989101544679443

theorem tailTrace_8151198 : CollatzResearch.WordTrace tailWord_8151198 prefixEnd_8151198 1395160827989101544679443 := by
  unfold tailWord_8151198
  simp only [CollatzResearch.WordTrace]
  refine ⟨37162326890451154328958781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198199076749072823087780165 37162326890451154328958781)
  ·
    refine ⟨13935872583919182873359543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37162326890451154328958781 13935872583919182873359543)
    ·
      refine ⟨20903808875878774310039315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13935872583919182873359543 20903808875878774310039315)
      ·
        refine ⟨31355713313818161465058973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20903808875878774310039315 31355713313818161465058973)
        ·
          refine ⟨11758392492681810549397115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31355713313818161465058973 11758392492681810549397115)
          ·
            refine ⟨17637588739022715824095673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11758392492681810549397115 17637588739022715824095673)
            ·
              refine ⟨13228191554267036868071755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17637588739022715824095673 13228191554267036868071755)
              ·
                refine ⟨19842287331400555302107633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13228191554267036868071755 19842287331400555302107633)
                ·
                  refine ⟨14881715498550416476580725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19842287331400555302107633 14881715498550416476580725)
                  ·
                    refine ⟨1395160827989101544679443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14881715498550416476580725 1395160827989101544679443)
                    ·
                      rfl

theorem cell23_8151198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_8151198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151198 prefixEnd_8151198 := by exact prefixLift 8151198
  have htrace : WordTrace (prefixWord ++ tailWord_8151198) baseStart_8151198 baseEnd_8151198 := by
    simpa [prefixWord, tailWord_8151198, baseEnd_8151198] using wordTrace_append hprefix tailTrace_8151198
  have hstable : (prefixWord ++ tailWord_8151198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151198).length < 2 ^ (prefixWord ++ tailWord_8151198).sum := by decide
  have hdescent : baseEnd_8151198 < baseStart_8151198 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151201 : List Nat := [1, 2, 3, 3, 1, 3, 2, 1, 2, 1, 4]
def baseStart_8151201 : Nat := 118140960795 + 8151201 * 2 ^ 59
def prefixEnd_8151201 : Nat := 4983230072969 + 3 ^ 40 * 8151201 * 2
def baseEnd_8151201 : Nat := 4185484024409268122300815

theorem tailTrace_8151201 : CollatzResearch.WordTrace tailWord_8151201 prefixEnd_8151201 4185484024409268122300815 := by
  unfold tailWord_8151201
  simp only [CollatzResearch.WordTrace]
  refine ⟨297298724542598366144029457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198199149695065577429352971 297298724542598366144029457)
  ·
    refine ⟨222974043406948774608022093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297298724542598366144029457 222974043406948774608022093)
    ·
      refine ⟨83615266277605790478008285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222974043406948774608022093 83615266277605790478008285)
      ·
        refine ⟨31355724854102171429253107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83615266277605790478008285 31355724854102171429253107)
        ·
          refine ⟨47033587281153257143879661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31355724854102171429253107 47033587281153257143879661)
          ·
            refine ⟨17637595230432471428954873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47033587281153257143879661 17637595230432471428954873)
            ·
              refine ⟨13228196422824353571716155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17637595230432471428954873 13228196422824353571716155)
              ·
                refine ⟨19842294634236530357574233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13228196422824353571716155 19842294634236530357574233)
                ·
                  refine ⟨14881720975677397768180675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19842294634236530357574233 14881720975677397768180675)
                  ·
                    refine ⟨22322581463516096652271013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14881720975677397768180675 22322581463516096652271013)
                    ·
                      refine ⟨4185484024409268122300815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22322581463516096652271013 4185484024409268122300815)
                      ·
                        rfl

theorem cell23_8151201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_8151201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151201 prefixEnd_8151201 := by exact prefixLift 8151201
  have htrace : WordTrace (prefixWord ++ tailWord_8151201) baseStart_8151201 baseEnd_8151201 := by
    simpa [prefixWord, tailWord_8151201, baseEnd_8151201] using wordTrace_append hprefix tailTrace_8151201
  have hstable : (prefixWord ++ tailWord_8151201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151201).length < 2 ^ (prefixWord ++ tailWord_8151201).sum := by decide
  have hdescent : baseEnd_8151201 < baseStart_8151201 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151224 : List Nat := [2, 1, 2, 1, 2, 1, 6, 2, 6]
def baseStart_8151224 : Nat := 118140960795 + 8151224 * 2 ^ 59
def prefixEnd_8151224 : Nat := 4983230072969 + 3 ^ 40 * 8151224 * 2
def baseEnd_8151224 : Nat := 465055092718257948034801

theorem tailTrace_8151224 : CollatzResearch.WordTrace tailWord_8151224 prefixEnd_8151224 465055092718257948034801 := by
  unfold tailWord_8151224
  simp only [CollatzResearch.WordTrace]
  refine ⟨148649781710757520536058363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198199708947676694048077817 148649781710757520536058363)
  ·
    refine ⟨222974672566136280804087545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148649781710757520536058363 222974672566136280804087545)
    ·
      refine ⟨167231004424602210603065659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222974672566136280804087545 167231004424602210603065659)
      ·
        refine ⟨250846506636903315904598489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167231004424602210603065659 250846506636903315904598489)
        ·
          refine ⟨188134879977677486928448867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250846506636903315904598489 188134879977677486928448867)
          ·
            refine ⟨282202319966516230392673301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188134879977677486928448867 282202319966516230392673301)
            ·
              refine ⟨13228233748430448299656561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 282202319966516230392673301 13228233748430448299656561)
              ·
                refine ⟨9921175311322836224742421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13228233748430448299656561 9921175311322836224742421)
                ·
                  refine ⟨465055092718257948034801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9921175311322836224742421 465055092718257948034801)
                  ·
                    rfl

theorem cell23_8151224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 2, 6].length) (baseStart_8151224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151224 prefixEnd_8151224 := by exact prefixLift 8151224
  have htrace : WordTrace (prefixWord ++ tailWord_8151224) baseStart_8151224 baseEnd_8151224 := by
    simpa [prefixWord, tailWord_8151224, baseEnd_8151224] using wordTrace_append hprefix tailTrace_8151224
  have hstable : (prefixWord ++ tailWord_8151224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151224).length < 2 ^ (prefixWord ++ tailWord_8151224).sum := by decide
  have hdescent : baseEnd_8151224 < baseStart_8151224 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151227 : List Nat := [1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 6]
def baseStart_8151227 : Nat := 118140960795 + 8151227 * 2 ^ 59
def prefixEnd_8151227 : Nat := 4983230072969 + 3 ^ 40 * 8151227 * 2
def baseEnd_8151227 : Nat := 4185497374906285020575695

theorem tailTrace_8151227 : CollatzResearch.WordTrace tailWord_8151227 prefixEnd_8151227 4185497374906285020575695 := by
  unfold tailWord_8151227
  simp only [CollatzResearch.WordTrace]
  refine ⟨297299672840504172584475935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198199781893669448389650623 297299672840504172584475935)
  ·
    refine ⟨445949509260756258876713903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297299672840504172584475935 445949509260756258876713903)
    ·
      refine ⟨668924263891134388315070855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445949509260756258876713903 668924263891134388315070855)
      ·
        refine ⟨1003386395836701582472606283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 668924263891134388315070855 1003386395836701582472606283)
        ·
          refine ⟨1505079593755052373708909425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1003386395836701582472606283 1505079593755052373708909425)
          ·
            refine ⟨1128809695316289280281682069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1505079593755052373708909425 1128809695316289280281682069)
            ·
              refine ⟨52912954467951060013203847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1128809695316289280281682069 52912954467951060013203847)
              ·
                refine ⟨79369431701926590019805771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52912954467951060013203847 79369431701926590019805771)
                ·
                  refine ⟨119054147552889885029708657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79369431701926590019805771 119054147552889885029708657)
                  ·
                    refine ⟨89290610664667413772281493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 119054147552889885029708657 89290610664667413772281493)
                    ·
                      refine ⟨4185497374906285020575695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89290610664667413772281493 4185497374906285020575695)
                      ·
                        rfl

theorem cell23_8151227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 6].length) (baseStart_8151227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151227 prefixEnd_8151227 := by exact prefixLift 8151227
  have htrace : WordTrace (prefixWord ++ tailWord_8151227) baseStart_8151227 baseEnd_8151227 := by
    simpa [prefixWord, tailWord_8151227, baseEnd_8151227] using wordTrace_append hprefix tailTrace_8151227
  have hstable : (prefixWord ++ tailWord_8151227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151227).length < 2 ^ (prefixWord ++ tailWord_8151227).sum := by decide
  have hdescent : baseEnd_8151227 < baseStart_8151227 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151247 : List Nat := [1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 7]
def baseStart_8151247 : Nat := 118140960795 + 8151247 * 2 ^ 59
def prefixEnd_8151247 : Nat := 4983230072969 + 3 ^ 40 * 8151247 * 2
def baseEnd_8151247 : Nat := 4185507644519374942325603

theorem tailTrace_8151247 : CollatzResearch.WordTrace tailWord_8151247 prefixEnd_8151247 4185507644519374942325603 := by
  unfold tailWord_8151247
  simp only [CollatzResearch.WordTrace]
  refine ⟨297300402300431716000203995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198200268200287810666802663 297300402300431716000203995)
  ·
    refine ⟨445950603450647574000305993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297300402300431716000203995 445950603450647574000305993)
    ·
      refine ⟨334462952587985680500229495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445950603450647574000305993 334462952587985680500229495)
      ·
        refine ⟨501694428881978520750344243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334462952587985680500229495 501694428881978520750344243)
        ·
          refine ⟨752541643322967781125516365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501694428881978520750344243 752541643322967781125516365)
          ·
            refine ⟨282203116246112917922068637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 752541643322967781125516365 282203116246112917922068637)
            ·
              refine ⟨105826168592292344220775739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 282203116246112917922068637 105826168592292344220775739)
              ·
                refine ⟨158739252888438516331163609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105826168592292344220775739 158739252888438516331163609)
                ·
                  refine ⟨119054439666328887248372707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158739252888438516331163609 119054439666328887248372707)
                  ·
                    refine ⟨178581659499493330872559061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 119054439666328887248372707 178581659499493330872559061)
                    ·
                      refine ⟨4185507644519374942325603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 178581659499493330872559061 4185507644519374942325603)
                      ·
                        rfl

theorem cell23_8151247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 7].length) (baseStart_8151247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151247 prefixEnd_8151247 := by exact prefixLift 8151247
  have htrace : WordTrace (prefixWord ++ tailWord_8151247) baseStart_8151247 baseEnd_8151247 := by
    simpa [prefixWord, tailWord_8151247, baseEnd_8151247] using wordTrace_append hprefix tailTrace_8151247
  have hstable : (prefixWord ++ tailWord_8151247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151247).length < 2 ^ (prefixWord ++ tailWord_8151247).sum := by decide
  have hdescent : baseEnd_8151247 < baseStart_8151247 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151308 : List Nat := [2, 2, 1, 2, 2, 2, 1, 4, 3, 2, 2]
def baseStart_8151308 : Nat := 118140960795 + 8151308 * 2 ^ 59
def prefixEnd_8151308 : Nat := 4983230072969 + 3 ^ 40 * 8151308 * 2
def baseEnd_8151308 : Nat := 4185538966839299203662823

theorem tailTrace_8151308 : CollatzResearch.WordTrace tailWord_8151308 prefixEnd_8151308 4185538966839299203662823 := by
  unfold tailWord_8151308
  simp only [CollatzResearch.WordTrace]
  refine ⟨148651313576605361709087289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198201751435473815612116385 148651313576605361709087289)
  ·
    refine ⟨111488485182454021281815467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148651313576605361709087289 111488485182454021281815467)
    ·
      refine ⟨167232727773681031922723201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111488485182454021281815467 167232727773681031922723201)
      ·
        refine ⟨125424545830260773942042401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167232727773681031922723201 125424545830260773942042401)
        ·
          refine ⟨94068409372695580456531801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125424545830260773942042401 94068409372695580456531801)
          ·
            refine ⟨70551307029521685342398851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94068409372695580456531801 70551307029521685342398851)
            ·
              refine ⟨105826960544282528013598277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70551307029521685342398851 105826960544282528013598277)
              ·
                refine ⟨19842555102052974002549677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105826960544282528013598277 19842555102052974002549677)
                ·
                  refine ⟨7440958163269865250956129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19842555102052974002549677 7440958163269865250956129)
                  ·
                    refine ⟨5580718622452398938217097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7440958163269865250956129 5580718622452398938217097)
                    ·
                      refine ⟨4185538966839299203662823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5580718622452398938217097 4185538966839299203662823)
                      ·
                        rfl

theorem cell23_8151308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 3, 2, 2].length) (baseStart_8151308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151308 prefixEnd_8151308 := by exact prefixLift 8151308
  have htrace : WordTrace (prefixWord ++ tailWord_8151308) baseStart_8151308 baseEnd_8151308 := by
    simpa [prefixWord, tailWord_8151308, baseEnd_8151308] using wordTrace_append hprefix tailTrace_8151308
  have hstable : (prefixWord ++ tailWord_8151308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151308).length < 2 ^ (prefixWord ++ tailWord_8151308).sum := by decide
  have hdescent : baseEnd_8151308 < baseStart_8151308 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151328 : List Nat := [2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 3]
def baseStart_8151328 : Nat := 118140960795 + 8151328 * 2 ^ 59
def prefixEnd_8151328 : Nat := 4983230072969 + 3 ^ 40 * 8151328 * 2
def baseEnd_8151328 : Nat := 4185549236452389125412731

theorem tailTrace_8151328 : CollatzResearch.WordTrace tailWord_8151328 prefixEnd_8151328 4185549236452389125412731 := by
  unfold tailWord_8151328
  simp only [CollatzResearch.WordTrace]
  refine ⟨148651678306569133416951319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198202237742092177889268425 148651678306569133416951319)
  ·
    refine ⟨222977517459853700125426979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148651678306569133416951319 222977517459853700125426979)
    ·
      refine ⟨334466276189780550188140469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222977517459853700125426979 334466276189780550188140469)
      ·
        refine ⟨31356213392791926580138169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 334466276189780550188140469 31356213392791926580138169)
        ·
          refine ⟨23517160044593944935103627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31356213392791926580138169 23517160044593944935103627)
          ·
            refine ⟨35275740066890917402655441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23517160044593944935103627 35275740066890917402655441)
            ·
              refine ⟨26456805050168188051991581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35275740066890917402655441 26456805050168188051991581)
              ·
                refine ⟨9921301893813070519496843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26456805050168188051991581 9921301893813070519496843)
                ·
                  refine ⟨14881952840719605779245265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9921301893813070519496843 14881952840719605779245265)
                  ·
                    refine ⟨11161464630539704334433949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14881952840719605779245265 11161464630539704334433949)
                    ·
                      refine ⟨4185549236452389125412731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11161464630539704334433949 4185549236452389125412731)
                      ·
                        rfl

theorem cell23_8151328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_8151328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151328 prefixEnd_8151328 := by exact prefixLift 8151328
  have htrace : WordTrace (prefixWord ++ tailWord_8151328) baseStart_8151328 baseEnd_8151328 := by
    simpa [prefixWord, tailWord_8151328, baseEnd_8151328] using wordTrace_append hprefix tailTrace_8151328
  have hstable : (prefixWord ++ tailWord_8151328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151328).length < 2 ^ (prefixWord ++ tailWord_8151328).sum := by decide
  have hdescent : baseEnd_8151328 < baseStart_8151328 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151374 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 3, 8]
def baseStart_8151374 : Nat := 118140960795 + 8151374 * 2 ^ 59
def prefixEnd_8151374 : Nat := 4983230072969 + 3 ^ 40 * 8151374 * 2
def baseEnd_8151374 : Nat := 1395190952187498648479173

theorem tailTrace_8151374 : CollatzResearch.WordTrace tailWord_8151374 prefixEnd_8151374 1395190952187498648479173 := by
  unfold tailWord_8151374
  simp only [CollatzResearch.WordTrace]
  refine ⟨37163129296371452086259647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198203356247314411126718117 37163129296371452086259647)
  ·
    refine ⟨55744693944557178129389471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37163129296371452086259647 55744693944557178129389471)
    ·
      refine ⟨83617040916835767194084207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55744693944557178129389471 83617040916835767194084207)
      ·
        refine ⟨125425561375253650791126311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83617040916835767194084207 125425561375253650791126311)
        ·
          refine ⟨188138342062880476186689467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125425561375253650791126311 188138342062880476186689467)
          ·
            refine ⟨282207513094320714280034201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188138342062880476186689467 282207513094320714280034201)
            ·
              refine ⟨211655634820740535710025651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282207513094320714280034201 211655634820740535710025651)
              ·
                refine ⟨317483452231110803565038477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211655634820740535710025651 317483452231110803565038477)
                ·
                  refine ⟨119056294586666551336889429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 317483452231110803565038477 119056294586666551336889429)
                  ·
                    refine ⟨1395190952187498648479173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 119056294586666551336889429 1395190952187498648479173)
                    ·
                      rfl

theorem cell23_8151374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 3, 8].length) (baseStart_8151374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151374 prefixEnd_8151374 := by exact prefixLift 8151374
  have htrace : WordTrace (prefixWord ++ tailWord_8151374) baseStart_8151374 baseEnd_8151374 := by
    simpa [prefixWord, tailWord_8151374, baseEnd_8151374] using wordTrace_append hprefix tailTrace_8151374
  have hstable : (prefixWord ++ tailWord_8151374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151374).length < 2 ^ (prefixWord ++ tailWord_8151374).sum := by decide
  have hdescent : baseEnd_8151374 < baseStart_8151374 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151384 : List Nat := [2, 1, 2, 2, 1, 1, 2, 3, 1, 3, 5]
def baseStart_8151384 : Nat := 118140960795 + 8151384 * 2 ^ 59
def prefixEnd_8151384 : Nat := 4983230072969 + 3 ^ 40 * 8151384 * 2
def baseEnd_8151384 : Nat := 4185577991369040906312473

theorem tailTrace_8151384 : CollatzResearch.WordTrace tailWord_8151384 prefixEnd_8151384 4185577991369040906312473 := by
  unfold tailWord_8151384
  simp only [CollatzResearch.WordTrace]
  refine ⟨148652699550467694198970603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198203599400623592265294137 148652699550467694198970603)
  ·
    refine ⟨222979049325701541298455905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148652699550467694198970603 222979049325701541298455905)
    ·
      refine ⟨167234286994276155973841929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222979049325701541298455905 167234286994276155973841929)
      ·
        refine ⟨125425715245707116980381447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167234286994276155973841929 125425715245707116980381447)
        ·
          refine ⟨188138572868560675470572171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125425715245707116980381447 188138572868560675470572171)
          ·
            refine ⟨282207859302841013205858257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188138572868560675470572171 282207859302841013205858257)
            ·
              refine ⟨211655894477130759904393693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282207859302841013205858257 211655894477130759904393693)
              ·
                refine ⟨79370960428924034964147635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211655894477130759904393693 79370960428924034964147635)
                ·
                  refine ⟨119056440643386052446221453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79370960428924034964147635 119056440643386052446221453)
                  ·
                    refine ⟨44646165241269769667333045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119056440643386052446221453 44646165241269769667333045)
                    ·
                      refine ⟨4185577991369040906312473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44646165241269769667333045 4185577991369040906312473)
                      ·
                        rfl

theorem cell23_8151384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_8151384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151384 prefixEnd_8151384 := by exact prefixLift 8151384
  have htrace : WordTrace (prefixWord ++ tailWord_8151384) baseStart_8151384 baseEnd_8151384 := by
    simpa [prefixWord, tailWord_8151384, baseEnd_8151384] using wordTrace_append hprefix tailTrace_8151384
  have hstable : (prefixWord ++ tailWord_8151384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151384).length < 2 ^ (prefixWord ++ tailWord_8151384).sum := by decide
  have hdescent : baseEnd_8151384 < baseStart_8151384 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151421 : List Nat := [1, 4, 1, 1, 2, 4, 1, 2, 7]
def baseStart_8151421 : Nat := 118140960795 + 8151421 * 2 ^ 59
def prefixEnd_8151421 : Nat := 4983230072969 + 3 ^ 40 * 8151421 * 2
def baseEnd_8151421 : Nat := 465066332239250806838867

theorem tailTrace_8151421 : CollatzResearch.WordTrace tailWord_8151421 prefixEnd_8151421 465066332239250806838867 := by
  unfold tailWord_8151421
  simp only [CollatzResearch.WordTrace]
  refine ⟨297306748601801343717038117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198204499067867562478025411 297306748601801343717038117)
  ·
    refine ⟨55745015362837751946944647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 297306748601801343717038117 55745015362837751946944647)
    ·
      refine ⟨83617523044256627920416971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55745015362837751946944647 83617523044256627920416971)
      ·
        refine ⟨125426284566384941880625457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83617523044256627920416971 125426284566384941880625457)
        ·
          refine ⟨94069713424788706410469093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125426284566384941880625457 94069713424788706410469093)
          ·
            refine ⟨17638071267147882451962955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94069713424788706410469093 17638071267147882451962955)
            ·
              refine ⟨26457106900721823677944433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17638071267147882451962955 26457106900721823677944433)
              ·
                refine ⟨19842830175541367758458325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26457106900721823677944433 19842830175541367758458325)
                ·
                  refine ⟨465066332239250806838867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19842830175541367758458325 465066332239250806838867)
                  ·
                    rfl

theorem cell23_8151421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 7].length) (baseStart_8151421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151421 prefixEnd_8151421 := by exact prefixLift 8151421
  have htrace : WordTrace (prefixWord ++ tailWord_8151421) baseStart_8151421 baseEnd_8151421 := by
    simpa [prefixWord, tailWord_8151421, baseEnd_8151421] using wordTrace_append hprefix tailTrace_8151421
  have hstable : (prefixWord ++ tailWord_8151421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151421).length < 2 ^ (prefixWord ++ tailWord_8151421).sum := by decide
  have hdescent : baseEnd_8151421 < baseStart_8151421 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151431 : List Nat := [1, 1, 4, 2, 2, 1, 1, 2, 1, 5, 3]
def baseStart_8151431 : Nat := 118140960795 + 8151431 * 2 ^ 59
def prefixEnd_8151431 : Nat := 4983230072969 + 3 ^ 40 * 8151431 * 2
def baseEnd_8151431 : Nat := 4185602124959802222424757

theorem tailTrace_8151431 : CollatzResearch.WordTrace tailWord_8151431 prefixEnd_8151431 4185602124959802222424757 := by
  unfold tailWord_8151431
  simp only [CollatzResearch.WordTrace]
  refine ⟨297307113331765115424902147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198204742221176743616601431 297307113331765115424902147)
  ·
    refine ⟨445960669997647673137353221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297307113331765115424902147 445960669997647673137353221)
    ·
      refine ⟨83617625624558938713253729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 445960669997647673137353221 83617625624558938713253729)
      ·
        refine ⟨62713219218419204034940297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83617625624558938713253729 62713219218419204034940297)
        ·
          refine ⟨47034914413814403026205223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62713219218419204034940297 47034914413814403026205223)
          ·
            refine ⟨70552371620721604539307835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47034914413814403026205223 70552371620721604539307835)
            ·
              refine ⟨105828557431082406808961753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70552371620721604539307835 105828557431082406808961753)
              ·
                refine ⟨79371418073311805106721315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105828557431082406808961753 79371418073311805106721315)
                ·
                  refine ⟨119057127109967707660081973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79371418073311805106721315 119057127109967707660081973)
                  ·
                    refine ⟨11161605666559472593132685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 119057127109967707660081973 11161605666559472593132685)
                    ·
                      refine ⟨4185602124959802222424757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11161605666559472593132685 4185602124959802222424757)
                      ·
                        rfl

theorem cell23_8151431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_8151431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151431 prefixEnd_8151431 := by exact prefixLift 8151431
  have htrace : WordTrace (prefixWord ++ tailWord_8151431) baseStart_8151431 baseEnd_8151431 := by
    simpa [prefixWord, tailWord_8151431, baseEnd_8151431] using wordTrace_append hprefix tailTrace_8151431
  have hstable : (prefixWord ++ tailWord_8151431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151431).length < 2 ^ (prefixWord ++ tailWord_8151431).sum := by decide
  have hdescent : baseEnd_8151431 < baseStart_8151431 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151448 : List Nat := [2, 1, 2, 5, 1, 1, 1, 2, 2, 3, 3]
def baseStart_8151448 : Nat := 118140960795 + 8151448 * 2 ^ 59
def prefixEnd_8151448 : Nat := 4983230072969 + 3 ^ 40 * 8151448 * 2
def baseEnd_8151448 : Nat := 4185610854130928655912179

theorem tailTrace_8151448 : CollatzResearch.WordTrace tailWord_8151448 prefixEnd_8151448 4185610854130928655912179 := by
  unfold tailWord_8151448
  simp only [CollatzResearch.WordTrace]
  refine ⟨148653866686351763664135499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198205155581802351552180665 148653866686351763664135499)
  ·
    refine ⟨222980800029527645496203249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148653866686351763664135499 222980800029527645496203249)
    ·
      refine ⟨167235600022145734122152437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222980800029527645496203249 167235600022145734122152437)
      ·
        refine ⟨15678337502076162573951791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 167235600022145734122152437 15678337502076162573951791)
        ·
          refine ⟨23517506253114243860927687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15678337502076162573951791 23517506253114243860927687)
          ·
            refine ⟨35276259379671365791391531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23517506253114243860927687 35276259379671365791391531)
            ·
              refine ⟨52914389069507048687087297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35276259379671365791391531 52914389069507048687087297)
              ·
                refine ⟨39685791802130286515315473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52914389069507048687087297 39685791802130286515315473)
                ·
                  refine ⟨29764343851597714886486605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39685791802130286515315473 29764343851597714886486605)
                  ·
                    refine ⟨11161628944349143082432477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29764343851597714886486605 11161628944349143082432477)
                    ·
                      refine ⟨4185610854130928655912179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11161628944349143082432477 4185610854130928655912179)
                      ·
                        rfl

theorem cell23_8151448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_8151448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151448 prefixEnd_8151448 := by exact prefixLift 8151448
  have htrace : WordTrace (prefixWord ++ tailWord_8151448) baseStart_8151448 baseEnd_8151448 := by
    simpa [prefixWord, tailWord_8151448, baseEnd_8151448] using wordTrace_append hprefix tailTrace_8151448
  have hstable : (prefixWord ++ tailWord_8151448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151448).length < 2 ^ (prefixWord ++ tailWord_8151448).sum := by decide
  have hdescent : baseEnd_8151448 < baseStart_8151448 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151466 : List Nat := [3, 1, 6, 1, 1, 2, 1, 1, 1, 4, 2]
def baseStart_8151466 : Nat := 118140960795 + 8151466 * 2 ^ 59
def prefixEnd_8151466 : Nat := 4983230072969 + 3 ^ 40 * 8151466 * 2
def baseEnd_8151466 : Nat := 4185620096782709585487097

theorem tailTrace_8151466 : CollatzResearch.WordTrace tailWord_8151466 prefixEnd_8151466 4185620096782709585487097 := by
  unfold tailWord_8151466
  simp only [CollatzResearch.WordTrace]
  refine ⟨74327097471659579100606563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198205593257758877601617501 74327097471659579100606563)
  ·
    refine ⟨111490646207489368650909845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74327097471659579100606563 111490646207489368650909845)
    ·
      refine ⟨5226124040976064155511399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 111490646207489368650909845 5226124040976064155511399)
      ·
        refine ⟨7839186061464096233267099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5226124040976064155511399 7839186061464096233267099)
        ·
          refine ⟨11758779092196144349900649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7839186061464096233267099 11758779092196144349900649)
          ·
            refine ⟨8819084319147108262425487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11758779092196144349900649 8819084319147108262425487)
            ·
              refine ⟨13228626478720662393638231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8819084319147108262425487 13228626478720662393638231)
              ·
                refine ⟨19842939718080993590457347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13228626478720662393638231 19842939718080993590457347)
                ·
                  refine ⟨29764409577121490385686021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19842939718080993590457347 29764409577121490385686021)
                  ·
                    refine ⟨5580826795710279447316129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29764409577121490385686021 5580826795710279447316129)
                    ·
                      refine ⟨4185620096782709585487097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5580826795710279447316129 4185620096782709585487097)
                      ·
                        rfl

theorem cell23_8151466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_8151466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151466 prefixEnd_8151466 := by exact prefixLift 8151466
  have htrace : WordTrace (prefixWord ++ tailWord_8151466) baseStart_8151466 baseEnd_8151466 := by
    simpa [prefixWord, tailWord_8151466, baseEnd_8151466] using wordTrace_append hprefix tailTrace_8151466
  have hstable : (prefixWord ++ tailWord_8151466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151466).length < 2 ^ (prefixWord ++ tailWord_8151466).sum := by decide
  have hdescent : baseEnd_8151466 < baseStart_8151466 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151528 : List Nat := [2, 1, 4, 1, 1, 4, 1, 3, 6]
def baseStart_8151528 : Nat := 118140960795 + 8151528 * 2 ^ 59
def prefixEnd_8151528 : Nat := 4983230072969 + 3 ^ 40 * 8151528 * 2
def baseEnd_8151528 : Nat := 465072436953698704767979

theorem tailTrace_8151528 : CollatzResearch.WordTrace tailWord_8151528 prefixEnd_8151528 465072436953698704767979 := by
  unfold tailWord_8151528
  simp only [CollatzResearch.WordTrace]
  refine ⟨148655325606206850495591619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198207100808275800660788825 148655325606206850495591619)
  ·
    refine ⟨222982988409310275743387429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148655325606206850495591619 222982988409310275743387429)
    ·
      refine ⟨41809310326745676701885143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222982988409310275743387429 41809310326745676701885143)
      ·
        refine ⟨62713965490118515052827715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41809310326745676701885143 62713965490118515052827715)
        ·
          refine ⟨94070948235177772579241573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62713965490118515052827715 94070948235177772579241573)
          ·
            refine ⟨17638302794095832358607795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94070948235177772579241573 17638302794095832358607795)
            ·
              refine ⟨26457454191143748537911693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17638302794095832358607795 26457454191143748537911693)
              ·
                refine ⟨9921545321678905701716885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26457454191143748537911693 9921545321678905701716885)
                ·
                  refine ⟨465072436953698704767979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9921545321678905701716885 465072436953698704767979)
                  ·
                    rfl

theorem cell23_8151528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 3, 6].length) (baseStart_8151528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151528 prefixEnd_8151528 := by exact prefixLift 8151528
  have htrace : WordTrace (prefixWord ++ tailWord_8151528) baseStart_8151528 baseEnd_8151528 := by
    simpa [prefixWord, tailWord_8151528, baseEnd_8151528] using wordTrace_append hprefix tailTrace_8151528
  have hstable : (prefixWord ++ tailWord_8151528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151528).length < 2 ^ (prefixWord ++ tailWord_8151528).sum := by decide
  have hdescent : baseEnd_8151528 < baseStart_8151528 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151571 : List Nat := [1, 1, 1, 2, 1, 5, 1, 2, 3, 6]
def baseStart_8151571 : Nat := 118140960795 + 8151571 * 2 ^ 59
def prefixEnd_8151571 : Nat := 4983230072969 + 3 ^ 40 * 8151571 * 2
def baseEnd_8151571 : Nat := 1395224670750477224891371

theorem tailTrace_8151571 : CollatzResearch.WordTrace tailWord_8151571 prefixEnd_8151571 1395224670750477224891371 := by
  unfold tailWord_8151571
  simp only [CollatzResearch.WordTrace]
  refine ⟨297312219551257919334998567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198208146367505279556665711 297312219551257919334998567)
  ·
    refine ⟨445968329326886879002497851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297312219551257919334998567 445968329326886879002497851)
    ·
      refine ⟨668952493990330318503746777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445968329326886879002497851 668952493990330318503746777)
      ·
        refine ⟨501714370492747738877810083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 668952493990330318503746777 501714370492747738877810083)
        ·
          refine ⟨752571555739121608316715125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501714370492747738877810083 752571555739121608316715125)
          ·
            refine ⟨70553583350542650779692043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 752571555739121608316715125 70553583350542650779692043)
            ·
              refine ⟨105830375025813976169538065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70553583350542650779692043 105830375025813976169538065)
              ·
                refine ⟨79372781269360482127153549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105830375025813976169538065 79372781269360482127153549)
                ·
                  refine ⟨29764792976010180797682581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79372781269360482127153549 29764792976010180797682581)
                  ·
                    refine ⟨1395224670750477224891371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29764792976010180797682581 1395224670750477224891371)
                    ·
                      rfl

theorem cell23_8151571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 6].length) (baseStart_8151571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151571 prefixEnd_8151571 := by exact prefixLift 8151571
  have htrace : WordTrace (prefixWord ++ tailWord_8151571) baseStart_8151571 baseEnd_8151571 := by
    simpa [prefixWord, tailWord_8151571, baseEnd_8151571] using wordTrace_append hprefix tailTrace_8151571
  have hstable : (prefixWord ++ tailWord_8151571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151571).length < 2 ^ (prefixWord ++ tailWord_8151571).sum := by decide
  have hdescent : baseEnd_8151571 < baseStart_8151571 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151578 : List Nat := [3, 1, 1, 3, 1, 1, 3, 2, 3, 1, 4]
def baseStart_8151578 : Nat := 118140960795 + 8151578 * 2 ^ 59
def prefixEnd_8151578 : Nat := 4983230072969 + 3 ^ 40 * 8151578 * 2
def baseEnd_8151578 : Nat := 4185677606616013147286581

theorem tailTrace_8151578 : CollatzResearch.WordTrace tailWord_8151578 prefixEnd_8151578 4185677606616013147286581 := by
  unfold tailWord_8151578
  simp only [CollatzResearch.WordTrace]
  refine ⟨74328118715558139882625847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198208316574821706353668925 74328118715558139882625847)
  ·
    refine ⟨111492178073337209823938771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74328118715558139882625847 111492178073337209823938771)
    ·
      refine ⟨167238267110005814735908157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111492178073337209823938771 167238267110005814735908157)
      ·
        refine ⟨62714350166252180525965559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167238267110005814735908157 62714350166252180525965559)
        ·
          refine ⟨94071525249378270788948339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62714350166252180525965559 94071525249378270788948339)
          ·
            refine ⟨141107287874067406183422509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94071525249378270788948339 141107287874067406183422509)
            ·
              refine ⟨52915232952775277318783441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141107287874067406183422509 52915232952775277318783441)
              ·
                refine ⟨39686424714581457989087581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52915232952775277318783441 39686424714581457989087581)
                ·
                  refine ⟨14882409267968046745907843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39686424714581457989087581 14882409267968046745907843)
                  ·
                    refine ⟨22323613901952070118861765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14882409267968046745907843 22323613901952070118861765)
                    ·
                      refine ⟨4185677606616013147286581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22323613901952070118861765 4185677606616013147286581)
                      ·
                        rfl

theorem cell23_8151578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_8151578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151578 prefixEnd_8151578 := by exact prefixLift 8151578
  have htrace : WordTrace (prefixWord ++ tailWord_8151578) baseStart_8151578 baseEnd_8151578 := by
    simpa [prefixWord, tailWord_8151578, baseEnd_8151578] using wordTrace_append hprefix tailTrace_8151578
  have hstable : (prefixWord ++ tailWord_8151578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151578).length < 2 ^ (prefixWord ++ tailWord_8151578).sum := by decide
  have hdescent : baseEnd_8151578 < baseStart_8151578 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151601 : List Nat := [1, 2, 2, 3, 1, 1, 2, 11]
def baseStart_8151601 : Nat := 118140960795 + 8151601 * 2 ^ 59
def prefixEnd_8151601 : Nat := 4983230072969 + 3 ^ 40 * 8151601 * 2
def baseEnd_8151601 : Nat := 155025533950780242862925

theorem tailTrace_8151601 : CollatzResearch.WordTrace tailWord_8151601 prefixEnd_8151601 155025533950780242862925 := by
  unfold tailWord_8151601
  simp only [CollatzResearch.WordTrace]
  refine ⟨297313313741149234458590657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198208875827432822972393771 297313313741149234458590657)
  ·
    refine ⟨222984985305861925843942993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297313313741149234458590657 222984985305861925843942993)
    ·
      refine ⟨167238738979396444382957245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222984985305861925843942993 167238738979396444382957245)
      ·
        refine ⟨62714527117273666643608967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167238738979396444382957245 62714527117273666643608967)
        ·
          refine ⟨94071790675910499965413451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62714527117273666643608967 94071790675910499965413451)
          ·
            refine ⟨141107686013865749948120177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94071790675910499965413451 141107686013865749948120177)
            ·
              refine ⟨105830764510399312461090133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141107686013865749948120177 105830764510399312461090133)
              ·
                refine ⟨155025533950780242862925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 105830764510399312461090133 155025533950780242862925)
                ·
                  rfl

theorem cell23_8151601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 11].length) (baseStart_8151601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151601 prefixEnd_8151601 := by exact prefixLift 8151601
  have htrace : WordTrace (prefixWord ++ tailWord_8151601) baseStart_8151601 baseEnd_8151601 := by
    simpa [prefixWord, tailWord_8151601, baseEnd_8151601] using wordTrace_append hprefix tailTrace_8151601
  have hstable : (prefixWord ++ tailWord_8151601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151601).length < 2 ^ (prefixWord ++ tailWord_8151601).sum := by decide
  have hdescent : baseEnd_8151601 < baseStart_8151601 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151606 : List Nat := [5, 1, 2, 1, 2, 2, 2, 3, 1, 1, 3]
def baseStart_8151606 : Nat := 118140960795 + 8151606 * 2 ^ 59
def prefixEnd_8151606 : Nat := 4983230072969 + 3 ^ 40 * 8151606 * 2
def baseEnd_8151606 : Nat := 4185691984074339037736453

theorem tailTrace_8151606 : CollatzResearch.WordTrace tailWord_8151606 prefixEnd_8151606 4185691984074339037736453 := by
  unfold tailWord_8151606
  simp only [CollatzResearch.WordTrace]
  refine ⟨18582093506633195019532667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198208997404087413541681781 18582093506633195019532667)
  ·
    refine ⟨27873140259949792529299001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18582093506633195019532667 27873140259949792529299001)
    ·
      refine ⟨20904855194962344396974251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27873140259949792529299001 20904855194962344396974251)
      ·
        refine ⟨31357282792443516595461377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20904855194962344396974251 31357282792443516595461377)
        ·
          refine ⟨23517962094332637446596033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31357282792443516595461377 23517962094332637446596033)
          ·
            refine ⟨17638471570749478084947025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23517962094332637446596033 17638471570749478084947025)
            ·
              refine ⟨13228853678062108563710269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17638471570749478084947025 13228853678062108563710269)
              ·
                refine ⟨4960820129273290711391351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13228853678062108563710269 4960820129273290711391351)
                ·
                  refine ⟨7441230193909936067087027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4960820129273290711391351 7441230193909936067087027)
                  ·
                    refine ⟨11161845290864904100630541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7441230193909936067087027 11161845290864904100630541)
                    ·
                      refine ⟨4185691984074339037736453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11161845290864904100630541 4185691984074339037736453)
                      ·
                        rfl

theorem cell23_8151606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_8151606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151606 prefixEnd_8151606 := by exact prefixLift 8151606
  have htrace : WordTrace (prefixWord ++ tailWord_8151606) baseStart_8151606 baseEnd_8151606 := by
    simpa [prefixWord, tailWord_8151606, baseEnd_8151606] using wordTrace_append hprefix tailTrace_8151606
  have hstable : (prefixWord ++ tailWord_8151606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151606).length < 2 ^ (prefixWord ++ tailWord_8151606).sum := by decide
  have hdescent : baseEnd_8151606 < baseStart_8151606 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151608 : List Nat := [2, 1, 2, 1, 4, 1, 1, 4, 1, 2, 4]
def baseStart_8151608 : Nat := 118140960795 + 8151608 * 2 ^ 59
def prefixEnd_8151608 : Nat := 4983230072969 + 3 ^ 40 * 8151608 * 2
def baseEnd_8151608 : Nat := 4185693011035648029911443

theorem tailTrace_8151608 : CollatzResearch.WordTrace tailWord_8151608 prefixEnd_8151608 4185693011035648029911443 := by
  unfold tailWord_8151608
  simp only [CollatzResearch.WordTrace]
  refine ⟨148656784526061937327047739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198209046034749249769396985 148656784526061937327047739)
  ·
    refine ⟨222985176789092905990571609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148656784526061937327047739 222985176789092905990571609)
    ·
      refine ⟨167238882591819679492928707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222985176789092905990571609 167238882591819679492928707)
      ·
        refine ⟨250858323887729519239393061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167238882591819679492928707 250858323887729519239393061)
        ·
          refine ⟨47035935728949284857386199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 250858323887729519239393061 47035935728949284857386199)
          ·
            refine ⟨70553903593423927286079299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47035935728949284857386199 70553903593423927286079299)
            ·
              refine ⟨105830855390135890929118949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70553903593423927286079299 105830855390135890929118949)
              ·
                refine ⟨19843285385650479549209803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105830855390135890929118949 19843285385650479549209803)
                ·
                  refine ⟨29764928078475719323814705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19843285385650479549209803 29764928078475719323814705)
                  ·
                    refine ⟨22323696058856789492861029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29764928078475719323814705 22323696058856789492861029)
                    ·
                      refine ⟨4185693011035648029911443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22323696058856789492861029 4185693011035648029911443)
                      ·
                        rfl

theorem cell23_8151608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 1, 2, 4].length) (baseStart_8151608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151608 prefixEnd_8151608 := by exact prefixLift 8151608
  have htrace : WordTrace (prefixWord ++ tailWord_8151608) baseStart_8151608 baseEnd_8151608 := by
    simpa [prefixWord, tailWord_8151608, baseEnd_8151608] using wordTrace_append hprefix tailTrace_8151608
  have hstable : (prefixWord ++ tailWord_8151608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151608).length < 2 ^ (prefixWord ++ tailWord_8151608).sum := by decide
  have hdescent : baseEnd_8151608 < baseStart_8151608 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151612 : List Nat := [2, 2, 2, 2, 3, 1, 4, 1, 1, 1, 4]
def baseStart_8151612 : Nat := 118140960795 + 8151612 * 2 ^ 59
def prefixEnd_8151612 : Nat := 4983230072969 + 3 ^ 40 * 8151612 * 2
def baseEnd_8151612 : Nat := 4185695064958266014261425

theorem tailTrace_8151612 : CollatzResearch.WordTrace tailWord_8151612 prefixEnd_8151612 4185695064958266014261425 := by
  unfold tailWord_8151612
  simp only [CollatzResearch.WordTrace]
  refine ⟨148656857472054691668620545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198209143296072922224827393 148656857472054691668620545)
  ·
    refine ⟨111492643104041018751465409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148656857472054691668620545 111492643104041018751465409)
    ·
      refine ⟨83619482328030764063599057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111492643104041018751465409 83619482328030764063599057)
      ·
        refine ⟨62714611746023073047699293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83619482328030764063599057 62714611746023073047699293)
        ·
          refine ⟨23517979404758652392887235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62714611746023073047699293 23517979404758652392887235)
          ·
            refine ⟨35276969107137978589330853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23517979404758652392887235 35276969107137978589330853)
            ·
              refine ⟨6614431707588370985499535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35276969107137978589330853 6614431707588370985499535)
              ·
                refine ⟨9921647561382556478249303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6614431707588370985499535 9921647561382556478249303)
                ·
                  refine ⟨14882471342073834717373955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9921647561382556478249303 14882471342073834717373955)
                  ·
                    refine ⟨22323707013110752076060933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14882471342073834717373955 22323707013110752076060933)
                    ·
                      refine ⟨4185695064958266014261425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22323707013110752076060933 4185695064958266014261425)
                      ·
                        rfl

theorem cell23_8151612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 1, 1, 1, 4].length) (baseStart_8151612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151612 prefixEnd_8151612 := by exact prefixLift 8151612
  have htrace : WordTrace (prefixWord ++ tailWord_8151612) baseStart_8151612 baseEnd_8151612 := by
    simpa [prefixWord, tailWord_8151612, baseEnd_8151612] using wordTrace_append hprefix tailTrace_8151612
  have hstable : (prefixWord ++ tailWord_8151612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151612).length < 2 ^ (prefixWord ++ tailWord_8151612).sum := by decide
  have hdescent : baseEnd_8151612 < baseStart_8151612 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151615 : List Nat := [1, 1, 2, 2, 3, 2, 3, 3, 1, 2, 3]
def baseStart_8151615 : Nat := 118140960795 + 8151615 * 2 ^ 59
def prefixEnd_8151615 : Nat := 4983230072969 + 3 ^ 40 * 8151615 * 2
def baseEnd_8151615 : Nat := 4185696605400229502523911

theorem tailTrace_8151615 : CollatzResearch.WordTrace tailWord_8151615 prefixEnd_8151615 4185696605400229502523911 := by
  unfold tailWord_8151615
  simp only [CollatzResearch.WordTrace]
  refine ⟨297313824363098514849600299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198209216242065676566400199 297313824363098514849600299)
  ·
    refine ⟨445970736544647772274400449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297313824363098514849600299 445970736544647772274400449)
    ·
      refine ⟨334478052408485829205800337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445970736544647772274400449 334478052408485829205800337)
      ·
        refine ⟨250858539306364371904350253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334478052408485829205800337 250858539306364371904350253)
        ·
          refine ⟨94071952239886639464131345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250858539306364371904350253 94071952239886639464131345)
          ·
            refine ⟨70553964179914979598098509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94071952239886639464131345 70553964179914979598098509)
            ·
              refine ⟨26457736567468117349286941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70553964179914979598098509 26457736567468117349286941)
              ·
                refine ⟨9921651212800544005982603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26457736567468117349286941 9921651212800544005982603)
                ·
                  refine ⟨14882476819200816008973905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9921651212800544005982603 14882476819200816008973905)
                  ·
                    refine ⟨11161857614400612006730429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14882476819200816008973905 11161857614400612006730429)
                    ·
                      refine ⟨4185696605400229502523911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11161857614400612006730429 4185696605400229502523911)
                      ·
                        rfl

theorem cell23_8151615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 3, 1, 2, 3].length) (baseStart_8151615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151615 prefixEnd_8151615 := by exact prefixLift 8151615
  have htrace : WordTrace (prefixWord ++ tailWord_8151615) baseStart_8151615 baseEnd_8151615 := by
    simpa [prefixWord, tailWord_8151615, baseEnd_8151615] using wordTrace_append hprefix tailTrace_8151615
  have hstable : (prefixWord ++ tailWord_8151615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151615).length < 2 ^ (prefixWord ++ tailWord_8151615).sum := by decide
  have hdescent : baseEnd_8151615 < baseStart_8151615 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151629 : List Nat := [1, 6, 1, 1, 2, 1, 1, 3, 3, 2, 2]
def baseStart_8151629 : Nat := 118140960795 + 8151629 * 2 ^ 59
def prefixEnd_8151629 : Nat := 4983230072969 + 3 ^ 40 * 8151629 * 2
def baseEnd_8151629 : Nat := 4185703794129392447748847

theorem tailTrace_8151629 : CollatzResearch.WordTrace tailWord_8151629 prefixEnd_8151629 4185703794129392447748847 := by
  unfold tailWord_8151629
  simp only [CollatzResearch.WordTrace]
  refine ⟨297314334985047795240609941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198209556656698530160406627 297314334985047795240609941)
  ·
    refine ⟨13936609452424115401903591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 297314334985047795240609941 13936609452424115401903591)
    ·
      refine ⟨20904914178636173102855387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13936609452424115401903591 20904914178636173102855387)
      ·
        refine ⟨31357371267954259654283081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20904914178636173102855387 31357371267954259654283081)
        ·
          refine ⟨23518028450965694740712311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31357371267954259654283081 23518028450965694740712311)
          ·
            refine ⟨35277042676448542111068467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23518028450965694740712311 35277042676448542111068467)
            ·
              refine ⟨52915564014672813166602701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35277042676448542111068467 52915564014672813166602701)
              ·
                refine ⟨19843336505502304937476013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52915564014672813166602701 19843336505502304937476013)
                ·
                  refine ⟨7441251189563364351553505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19843336505502304937476013 7441251189563364351553505)
                  ·
                    refine ⟨5580938392172523263665129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7441251189563364351553505 5580938392172523263665129)
                    ·
                      refine ⟨4185703794129392447748847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5580938392172523263665129 4185703794129392447748847)
                      ·
                        rfl

theorem cell23_8151629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_8151629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151629 prefixEnd_8151629 := by exact prefixLift 8151629
  have htrace : WordTrace (prefixWord ++ tailWord_8151629) baseStart_8151629 baseEnd_8151629 := by
    simpa [prefixWord, tailWord_8151629, baseEnd_8151629] using wordTrace_append hprefix tailTrace_8151629
  have hstable : (prefixWord ++ tailWord_8151629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151629).length < 2 ^ (prefixWord ++ tailWord_8151629).sum := by decide
  have hdescent : baseEnd_8151629 < baseStart_8151629 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151631 : List Nat := [1, 1, 2, 1, 1, 2, 4, 1, 1, 9]
def baseStart_8151631 : Nat := 118140960795 + 8151631 * 2 ^ 59
def prefixEnd_8151631 : Nat := 4983230072969 + 3 ^ 40 * 8151631 * 2
def baseEnd_8151631 : Nat := 1395234940363567146641279

theorem tailTrace_8151631 : CollatzResearch.WordTrace tailWord_8151631 prefixEnd_8151631 1395234940363567146641279 := by
  unfold tailWord_8151631
  simp only [CollatzResearch.WordTrace]
  refine ⟨297314407931040549582182747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198209605287360366388121831 297314407931040549582182747)
  ·
    refine ⟨445971611896560824373274121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297314407931040549582182747 445971611896560824373274121)
    ·
      refine ⟨334478708922420618279955591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445971611896560824373274121 334478708922420618279955591)
      ·
        refine ⟨501718063383630927419933387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334478708922420618279955591 501718063383630927419933387)
        ·
          refine ⟨752577095075446391129900081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501718063383630927419933387 752577095075446391129900081)
          ·
            refine ⟨564432821306584793347425061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 752577095075446391129900081 564432821306584793347425061)
            ·
              refine ⟨105831153994984648752642199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 564432821306584793347425061 105831153994984648752642199)
              ·
                refine ⟨158746730992476973128963299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105831153994984648752642199 158746730992476973128963299)
                ·
                  refine ⟨238120096488715459693444949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158746730992476973128963299 238120096488715459693444949)
                  ·
                    refine ⟨1395234940363567146641279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 238120096488715459693444949 1395234940363567146641279)
                    ·
                      rfl

theorem cell23_8151631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 9].length) (baseStart_8151631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151631 prefixEnd_8151631 := by exact prefixLift 8151631
  have htrace : WordTrace (prefixWord ++ tailWord_8151631) baseStart_8151631 baseEnd_8151631 := by
    simpa [prefixWord, tailWord_8151631, baseEnd_8151631] using wordTrace_append hprefix tailTrace_8151631
  have hstable : (prefixWord ++ tailWord_8151631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151631).length < 2 ^ (prefixWord ++ tailWord_8151631).sum := by decide
  have hdescent : baseEnd_8151631 < baseStart_8151631 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151658 : List Nat := [3, 1, 3, 2, 1, 1, 1, 1, 1, 4, 5]
def baseStart_8151658 : Nat := 118140960795 + 8151658 * 2 ^ 59
def prefixEnd_8151658 : Nat := 4983230072969 + 3 ^ 40 * 8151658 * 2
def baseEnd_8151658 : Nat := 4185718685068372834286213

theorem tailTrace_8151658 : CollatzResearch.WordTrace tailWord_8151658 prefixEnd_8151658 4185718685068372834286213 := by
  unfold tailWord_8151658
  simp only [CollatzResearch.WordTrace]
  refine ⟨74328848175485683298353907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198210261801295155462277085 74328848175485683298353907)
  ·
    refine ⟨111493272263228524947530861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74328848175485683298353907 111493272263228524947530861)
    ·
      refine ⟨41809977098710696855324073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111493272263228524947530861 41809977098710696855324073)
      ·
        refine ⟨31357482824033022641493055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41809977098710696855324073 31357482824033022641493055)
        ·
          refine ⟨47036224236049533962239583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31357482824033022641493055 47036224236049533962239583)
          ·
            refine ⟨70554336354074300943359375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47036224236049533962239583 70554336354074300943359375)
            ·
              refine ⟨105831504531111451415039063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70554336354074300943359375 105831504531111451415039063)
              ·
                refine ⟨158747256796667177122558595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105831504531111451415039063 158747256796667177122558595)
                ·
                  refine ⟨238120885195000765683837893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158747256796667177122558595 238120885195000765683837893)
                  ·
                    refine ⟨44647665974062643565719605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 238120885195000765683837893 44647665974062643565719605)
                    ·
                      refine ⟨4185718685068372834286213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44647665974062643565719605 4185718685068372834286213)
                      ·
                        rfl

theorem cell23_8151658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_8151658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151658 prefixEnd_8151658 := by exact prefixLift 8151658
  have htrace : WordTrace (prefixWord ++ tailWord_8151658) baseStart_8151658 baseEnd_8151658 := by
    simpa [prefixWord, tailWord_8151658, baseEnd_8151658] using wordTrace_append hprefix tailTrace_8151658
  have hstable : (prefixWord ++ tailWord_8151658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151658).length < 2 ^ (prefixWord ++ tailWord_8151658).sum := by decide
  have hdescent : baseEnd_8151658 < baseStart_8151658 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151662 : List Nat := [4, 1, 2, 2, 2, 1, 1, 2, 4, 1, 3]
def baseStart_8151662 : Nat := 118140960795 + 8151662 * 2 ^ 59
def prefixEnd_8151662 : Nat := 4983230072969 + 3 ^ 40 * 8151662 * 2
def baseEnd_8151662 : Nat := 4185720738990990818636195

theorem tailTrace_8151662 : CollatzResearch.WordTrace tailWord_8151662 prefixEnd_8151662 4185720738990990818636195 := by
  unfold tailWord_8151662
  simp only [CollatzResearch.WordTrace]
  refine ⟨37164442324241030234570155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198210359062618827917707493 37164442324241030234570155)
  ·
    refine ⟨55746663486361545351855233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37164442324241030234570155 55746663486361545351855233)
    ·
      refine ⟨41809997614771159013891425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55746663486361545351855233 41809997614771159013891425)
      ·
        refine ⟨31357498211078369260418569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41809997614771159013891425 31357498211078369260418569)
        ·
          refine ⟨23518123658308776945313927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31357498211078369260418569 23518123658308776945313927)
          ·
            refine ⟨35277185487463165417970891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23518123658308776945313927 35277185487463165417970891)
            ·
              refine ⟨52915778231194748126956337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35277185487463165417970891 52915778231194748126956337)
              ·
                refine ⟨39686833673396061095217253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52915778231194748126956337 39686833673396061095217253)
                ·
                  refine ⟨7441281313761761455353235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39686833673396061095217253 7441281313761761455353235)
                  ·
                    refine ⟨11161921970642642183029853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7441281313761761455353235 11161921970642642183029853)
                    ·
                      refine ⟨4185720738990990818636195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11161921970642642183029853 4185720738990990818636195)
                      ·
                        rfl

theorem cell23_8151662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_8151662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151662 prefixEnd_8151662 := by exact prefixLift 8151662
  have htrace : WordTrace (prefixWord ++ tailWord_8151662) baseStart_8151662 baseEnd_8151662 := by
    simpa [prefixWord, tailWord_8151662, baseEnd_8151662] using wordTrace_append hprefix tailTrace_8151662
  have hstable : (prefixWord ++ tailWord_8151662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151662).length < 2 ^ (prefixWord ++ tailWord_8151662).sum := by decide
  have hdescent : baseEnd_8151662 < baseStart_8151662 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151742 : List Nat := [4, 2, 1, 1, 2, 1, 3, 4, 5]
def baseStart_8151742 : Nat := 118140960795 + 8151742 * 2 ^ 59
def prefixEnd_8151742 : Nat := 4983230072969 + 3 ^ 40 * 8151742 * 2
def baseEnd_8151742 : Nat := 465084646382594500626203

theorem tailTrace_8151742 : CollatzResearch.WordTrace tailWord_8151742 prefixEnd_8151742 465084646382594500626203 := by
  unfold tailWord_8151742
  simp only [CollatzResearch.WordTrace]
  refine ⟨37164807054204801942434185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198212304289092277026315653 37164807054204801942434185)
  ·
    refine ⟨27873605290653601456825639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37164807054204801942434185 27873605290653601456825639)
    ·
      refine ⟨41810407935980402185238459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27873605290653601456825639 41810407935980402185238459)
      ·
        refine ⟨62715611903970603277857689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41810407935980402185238459 62715611903970603277857689)
        ·
          refine ⟨47036708927977952458393267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62715611903970603277857689 47036708927977952458393267)
          ·
            refine ⟨70555063391966928687589901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47036708927977952458393267 70555063391966928687589901)
            ·
              refine ⟨26458148771987598257846213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70555063391966928687589901 26458148771987598257846213)
              ·
                refine ⟨4960902894747674673346165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26458148771987598257846213 4960902894747674673346165)
                ·
                  refine ⟨465084646382594500626203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4960902894747674673346165 465084646382594500626203)
                  ·
                    rfl

theorem cell23_8151742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 4, 5].length) (baseStart_8151742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151742 prefixEnd_8151742 := by exact prefixLift 8151742
  have htrace : WordTrace (prefixWord ++ tailWord_8151742) baseStart_8151742 baseEnd_8151742 := by
    simpa [prefixWord, tailWord_8151742, baseEnd_8151742] using wordTrace_append hprefix tailTrace_8151742
  have hstable : (prefixWord ++ tailWord_8151742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151742).length < 2 ^ (prefixWord ++ tailWord_8151742).sum := by decide
  have hdescent : baseEnd_8151742 < baseStart_8151742 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151772 : List Nat := [2, 2, 5, 1, 1, 2, 1, 1, 1, 7]
def baseStart_8151772 : Nat := 118140960795 + 8151772 * 2 ^ 59
def prefixEnd_8151772 : Nat := 4983230072969 + 3 ^ 40 * 8151772 * 2
def baseEnd_8151772 : Nat := 1395259073954328462753563

theorem tailTrace_8151772 : CollatzResearch.WordTrace tailWord_8151772 prefixEnd_8151772 1395259073954328462753563 := by
  unfold tailWord_8151772
  simp only [CollatzResearch.WordTrace]
  refine ⟨148659775311764865331532785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198213033749019820442043713 148659775311764865331532785)
  ·
    refine ⟨111494831483823648998649589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148659775311764865331532785 111494831483823648998649589)
    ·
      refine ⟨10452640451608467093623399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111494831483823648998649589 10452640451608467093623399)
      ·
        refine ⟨15678960677412700640435099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10452640451608467093623399 15678960677412700640435099)
        ·
          refine ⟨23518441016119050960652649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15678960677412700640435099 23518441016119050960652649)
          ·
            refine ⟨17638830762089288220489487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23518441016119050960652649 17638830762089288220489487)
            ·
              refine ⟨26458246143133932330734231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17638830762089288220489487 26458246143133932330734231)
              ·
                refine ⟨39687369214700898496101347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26458246143133932330734231 39687369214700898496101347)
                ·
                  refine ⟨59531053822051347744152021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39687369214700898496101347 59531053822051347744152021)
                  ·
                    refine ⟨1395259073954328462753563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59531053822051347744152021 1395259073954328462753563)
                    ·
                      rfl

theorem cell23_8151772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_8151772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151772 prefixEnd_8151772 := by exact prefixLift 8151772
  have htrace : WordTrace (prefixWord ++ tailWord_8151772) baseStart_8151772 baseEnd_8151772 := by
    simpa [prefixWord, tailWord_8151772, baseEnd_8151772] using wordTrace_append hprefix tailTrace_8151772
  have hstable : (prefixWord ++ tailWord_8151772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151772).length < 2 ^ (prefixWord ++ tailWord_8151772).sum := by decide
  have hdescent : baseEnd_8151772 < baseStart_8151772 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151775 : List Nat := [1, 1, 2, 3, 2, 4, 1, 1, 1, 3, 4]
def baseStart_8151775 : Nat := 118140960795 + 8151775 * 2 ^ 59
def prefixEnd_8151775 : Nat := 4983230072969 + 3 ^ 40 * 8151775 * 2
def baseEnd_8151775 : Nat := 4185778762304948876523175

theorem tailTrace_8151775 : CollatzResearch.WordTrace tailWord_8151775 prefixEnd_8151775 4185778762304948876523175 := by
  unfold tailWord_8151775
  simp only [CollatzResearch.WordTrace]
  refine ⟨297319660042518862175424779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198213106695012574783616519 297319660042518862175424779)
  ·
    refine ⟨445979490063778293263137169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297319660042518862175424779 445979490063778293263137169)
    ·
      refine ⟨334484617547833719947352877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445979490063778293263137169 334484617547833719947352877)
      ·
        refine ⟨125431731580437644980257329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334484617547833719947352877 125431731580437644980257329)
        ·
          refine ⟨94073798685328233735192997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125431731580437644980257329 94073798685328233735192997)
          ·
            refine ⟨17638837253499043825348687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94073798685328233735192997 17638837253499043825348687)
            ·
              refine ⟨26458255880248565738023031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17638837253499043825348687 26458255880248565738023031)
              ·
                refine ⟨39687383820372848607034547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26458255880248565738023031 39687383820372848607034547)
                ·
                  refine ⟨59531075730559272910551821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39687383820372848607034547 59531075730559272910551821)
                  ·
                    refine ⟨22324153398959727341456933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59531075730559272910551821 22324153398959727341456933)
                    ·
                      refine ⟨4185778762304948876523175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22324153398959727341456933 4185778762304948876523175)
                      ·
                        rfl

theorem cell23_8151775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_8151775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151775 prefixEnd_8151775 := by exact prefixLift 8151775
  have htrace : WordTrace (prefixWord ++ tailWord_8151775) baseStart_8151775 baseEnd_8151775 := by
    simpa [prefixWord, tailWord_8151775, baseEnd_8151775] using wordTrace_append hprefix tailTrace_8151775
  have hstable : (prefixWord ++ tailWord_8151775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151775).length < 2 ^ (prefixWord ++ tailWord_8151775).sum := by decide
  have hdescent : baseEnd_8151775 < baseStart_8151775 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151795 : List Nat := [1, 1, 1, 2, 2, 3, 1, 3, 4, 2, 3]
def baseStart_8151795 : Nat := 118140960795 + 8151795 * 2 ^ 59
def prefixEnd_8151795 : Nat := 4983230072969 + 3 ^ 40 * 8151795 * 2
def baseEnd_8151795 : Nat := 4185789031918038798273083

theorem tailTrace_8151795 : CollatzResearch.WordTrace tailWord_8151795 prefixEnd_8151795 4185789031918038798273083 := by
  unfold tailWord_8151795
  simp only [CollatzResearch.WordTrace]
  refine ⟨297320389502446405591152839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198213593001630937060768559 297320389502446405591152839)
  ·
    refine ⟨445980584253669608386729259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297320389502446405591152839 445980584253669608386729259)
    ·
      refine ⟨668970876380504412580093889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445980584253669608386729259 668970876380504412580093889)
      ·
        refine ⟨501728157285378309435070417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 668970876380504412580093889 501728157285378309435070417)
        ·
          refine ⟨376296117964033732076302813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 501728157285378309435070417 376296117964033732076302813)
          ·
            refine ⟨141111044236512649528613555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 376296117964033732076302813 141111044236512649528613555)
            ·
              refine ⟨211666566354768974292920333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141111044236512649528613555 211666566354768974292920333)
              ·
                refine ⟨79374962383038365359845125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211666566354768974292920333 79374962383038365359845125)
                ·
                  refine ⟨14882805446819693504970961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79374962383038365359845125 14882805446819693504970961)
                  ·
                    refine ⟨11162104085114770128728221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14882805446819693504970961 11162104085114770128728221)
                    ·
                      refine ⟨4185789031918038798273083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11162104085114770128728221 4185789031918038798273083)
                      ·
                        rfl

theorem cell23_8151795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 4, 2, 3].length) (baseStart_8151795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151795 prefixEnd_8151795 := by exact prefixLift 8151795
  have htrace : WordTrace (prefixWord ++ tailWord_8151795) baseStart_8151795 baseEnd_8151795 := by
    simpa [prefixWord, tailWord_8151795, baseEnd_8151795] using wordTrace_append hprefix tailTrace_8151795
  have hstable : (prefixWord ++ tailWord_8151795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151795).length < 2 ^ (prefixWord ++ tailWord_8151795).sum := by decide
  have hdescent : baseEnd_8151795 < baseStart_8151795 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151836 : List Nat := [2, 2, 3, 1, 1, 5, 1, 3, 1, 4]
def baseStart_8151836 : Nat := 118140960795 + 8151836 * 2 ^ 59
def prefixEnd_8151836 : Nat := 4983230072969 + 3 ^ 40 * 8151836 * 2
def baseEnd_8151836 : Nat := 1395270028208291045953465

theorem tailTrace_8151836 : CollatzResearch.WordTrace tailWord_8151836 prefixEnd_8151836 1395270028208291045953465 := by
  unfold tailWord_8151836
  simp only [CollatzResearch.WordTrace]
  refine ⟨148660942447648934796697681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198214589930198579728930241 148660942447648934796697681)
  ·
    refine ⟨111495706835736701097523261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148660942447648934796697681 111495706835736701097523261)
    ·
      refine ⟨41810890063401262911571223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111495706835736701097523261 41810890063401262911571223)
      ·
        refine ⟨62716335095101894367356835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41810890063401262911571223 62716335095101894367356835)
        ·
          refine ⟨94074502642652841551035253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62716335095101894367356835 94074502642652841551035253)
          ·
            refine ⟨8819484622748703895409555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94074502642652841551035253 8819484622748703895409555)
            ·
              refine ⟨13229226934123055843114333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8819484622748703895409555 13229226934123055843114333)
              ·
                refine ⟨4960960100296145941167875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13229226934123055843114333 4960960100296145941167875)
                ·
                  refine ⟨7441440150444218911751813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4960960100296145941167875 7441440150444218911751813)
                  ·
                    refine ⟨1395270028208291045953465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7441440150444218911751813 1395270028208291045953465)
                    ·
                      rfl

theorem cell23_8151836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_8151836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151836 prefixEnd_8151836 := by exact prefixLift 8151836
  have htrace : WordTrace (prefixWord ++ tailWord_8151836) baseStart_8151836 baseEnd_8151836 := by
    simpa [prefixWord, tailWord_8151836, baseEnd_8151836] using wordTrace_append hprefix tailTrace_8151836
  have hstable : (prefixWord ++ tailWord_8151836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151836).length < 2 ^ (prefixWord ++ tailWord_8151836).sum := by decide
  have hdescent : baseEnd_8151836 < baseStart_8151836 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151853 : List Nat := [1, 5, 3, 2, 1, 2, 1, 1, 3, 4]
def baseStart_8151853 : Nat := 118140960795 + 8151853 * 2 ^ 59
def prefixEnd_8151853 : Nat := 4983230072969 + 3 ^ 40 * 8151853 * 2
def baseEnd_8151853 : Nat := 1395272937931999857115939

theorem tailTrace_8151853 : CollatzResearch.WordTrace tailWord_8151853 prefixEnd_8151853 1395272937931999857115939 := by
  unfold tailWord_8151853
  simp only [CollatzResearch.WordTrace]
  refine ⟨297322504936236281496764213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198215003290824187664509475 297322504936236281496764213)
  ·
    refine ⟨27873984837772151390321645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 297322504936236281496764213 27873984837772151390321645)
    ·
      refine ⟨10452744314164556771370617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27873984837772151390321645 10452744314164556771370617)
      ·
        refine ⟨7839558235623417578527963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10452744314164556771370617 7839558235623417578527963)
        ·
          refine ⟨11759337353435126367791945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7839558235623417578527963 11759337353435126367791945)
          ·
            refine ⟨8819503015076344775843959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11759337353435126367791945 8819503015076344775843959)
            ·
              refine ⟨13229254522614517163765939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8819503015076344775843959 13229254522614517163765939)
              ·
                refine ⟨19843881783921775745648909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13229254522614517163765939 19843881783921775745648909)
                ·
                  refine ⟨7441455668970665904618341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19843881783921775745648909 7441455668970665904618341)
                  ·
                    refine ⟨1395272937931999857115939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7441455668970665904618341 1395272937931999857115939)
                    ·
                      rfl

theorem cell23_8151853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_8151853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151853 prefixEnd_8151853 := by exact prefixLift 8151853
  have htrace : WordTrace (prefixWord ++ tailWord_8151853) baseStart_8151853 baseEnd_8151853 := by
    simpa [prefixWord, tailWord_8151853, baseEnd_8151853] using wordTrace_append hprefix tailTrace_8151853
  have hstable : (prefixWord ++ tailWord_8151853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151853).length < 2 ^ (prefixWord ++ tailWord_8151853).sum := by decide
  have hdescent : baseEnd_8151853 < baseStart_8151853 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151859 : List Nat := [1, 1, 1, 2, 6, 1, 3, 1, 3, 1, 3]
def baseStart_8151859 : Nat := 118140960795 + 8151859 * 2 ^ 59
def prefixEnd_8151859 : Nat := 4983230072969 + 3 ^ 40 * 8151859 * 2
def baseEnd_8151859 : Nat := 4185821894679926547872789

theorem tailTrace_8151859 : CollatzResearch.WordTrace tailWord_8151859 prefixEnd_8151859 4185821894679926547872789 := by
  unfold tailWord_8151859
  simp only [CollatzResearch.WordTrace]
  refine ⟨297322723774214544521482631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198215149182809696347655087 297322723774214544521482631)
  ·
    refine ⟨445984085661321816782223947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297322723774214544521482631 445984085661321816782223947)
    ·
      refine ⟨668976128491982725173335921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445984085661321816782223947 668976128491982725173335921)
      ·
        refine ⟨501732096368987043880001941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 668976128491982725173335921 501732096368987043880001941)
        ·
          refine ⟨23518692017296267681875091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 501732096368987043880001941 23518692017296267681875091)
          ·
            refine ⟨35278038025944401522812637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23518692017296267681875091 35278038025944401522812637)
            ·
              refine ⟨13229264259729150571054739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35278038025944401522812637 13229264259729150571054739)
              ·
                refine ⟨19843896389593725856582109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13229264259729150571054739 19843896389593725856582109)
                ·
                  refine ⟨7441461146097647196218291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19843896389593725856582109 7441461146097647196218291)
                  ·
                    refine ⟨11162191719146470794327437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7441461146097647196218291 11162191719146470794327437)
                    ·
                      refine ⟨4185821894679926547872789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11162191719146470794327437 4185821894679926547872789)
                      ·
                        rfl

theorem cell23_8151859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 3, 1, 3].length) (baseStart_8151859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151859 prefixEnd_8151859 := by exact prefixLift 8151859
  have htrace : WordTrace (prefixWord ++ tailWord_8151859) baseStart_8151859 baseEnd_8151859 := by
    simpa [prefixWord, tailWord_8151859, baseEnd_8151859] using wordTrace_append hprefix tailTrace_8151859
  have hstable : (prefixWord ++ tailWord_8151859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151859).length < 2 ^ (prefixWord ++ tailWord_8151859).sum := by decide
  have hdescent : baseEnd_8151859 < baseStart_8151859 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151866 : List Nat := [3, 1, 1, 1, 7, 1, 2, 1, 6]
def baseStart_8151866 : Nat := 118140960795 + 8151866 * 2 ^ 59
def prefixEnd_8151866 : Nat := 4983230072969 + 3 ^ 40 * 8151866 * 2
def baseEnd_8151866 : Nat := 465091721004945335609473

theorem tailTrace_8151866 : CollatzResearch.WordTrace tailWord_8151866 prefixEnd_8151866 465091721004945335609473 := by
  unfold tailWord_8151866
  simp only [CollatzResearch.WordTrace]
  refine ⟨74330744771297296179246863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198215319390126123144658301 74330744771297296179246863)
  ·
    refine ⟨111496117156945944268870295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74330744771297296179246863 111496117156945944268870295)
    ·
      refine ⟨167244175735418916403305443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111496117156945944268870295 167244175735418916403305443)
      ·
        refine ⟨250866263603128374604958165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167244175735418916403305443 250866263603128374604958165)
        ·
          refine ⟨5879678053198321279803707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 250866263603128374604958165 5879678053198321279803707)
          ·
            refine ⟨8819517079797481919705561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5879678053198321279803707 8819517079797481919705561)
            ·
              refine ⟨6614637809848111439779171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8819517079797481919705561 6614637809848111439779171)
              ·
                refine ⟨9921956714772167159668757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6614637809848111439779171 9921956714772167159668757)
                ·
                  refine ⟨465091721004945335609473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9921956714772167159668757 465091721004945335609473)
                  ·
                    rfl

theorem cell23_8151866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 1, 6].length) (baseStart_8151866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151866 prefixEnd_8151866 := by exact prefixLift 8151866
  have htrace : WordTrace (prefixWord ++ tailWord_8151866) baseStart_8151866 baseEnd_8151866 := by
    simpa [prefixWord, tailWord_8151866, baseEnd_8151866] using wordTrace_append hprefix tailTrace_8151866
  have hstable : (prefixWord ++ tailWord_8151866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151866).length < 2 ^ (prefixWord ++ tailWord_8151866).sum := by decide
  have hdescent : baseEnd_8151866 < baseStart_8151866 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151875 : List Nat := [1, 1, 1, 3, 1, 4, 2, 3, 1, 6]
def baseStart_8151875 : Nat := 118140960795 + 8151875 * 2 ^ 59
def prefixEnd_8151875 : Nat := 4983230072969 + 3 ^ 40 * 8151875 * 2
def baseEnd_8151875 : Nat := 1395276703456799495090905

theorem tailTrace_8151875 : CollatzResearch.WordTrace tailWord_8151875 prefixEnd_8151875 1395276703456799495090905 := by
  unfold tailWord_8151875
  simp only [CollatzResearch.WordTrace]
  refine ⟨297323307342156579254065079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198215538228104386169376719 297323307342156579254065079)
  ·
    refine ⟨445984961013234868881097619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297323307342156579254065079 445984961013234868881097619)
    ·
      refine ⟨668977441519852303321646429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445984961013234868881097619 668977441519852303321646429)
      ·
        refine ⟨250866540569944613745617411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 668977441519852303321646429 250866540569944613745617411)
        ·
          refine ⟨376299810854916920618426117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250866540569944613745617411 376299810854916920618426117)
          ·
            refine ⟨70556214535296922615954897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 376299810854916920618426117 70556214535296922615954897)
            ·
              refine ⟨52917160901472691961966173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70556214535296922615954897 52917160901472691961966173)
              ·
                refine ⟨19843935338052259485737315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52917160901472691961966173 19843935338052259485737315)
                ·
                  refine ⟨29765903007078389228605973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19843935338052259485737315 29765903007078389228605973)
                  ·
                    refine ⟨1395276703456799495090905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29765903007078389228605973 1395276703456799495090905)
                    ·
                      rfl

theorem cell23_8151875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 6].length) (baseStart_8151875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151875 prefixEnd_8151875 := by exact prefixLift 8151875
  have htrace : WordTrace (prefixWord ++ tailWord_8151875) baseStart_8151875 baseEnd_8151875 := by
    simpa [prefixWord, tailWord_8151875, baseEnd_8151875] using wordTrace_append hprefix tailTrace_8151875
  have hstable : (prefixWord ++ tailWord_8151875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151875).length < 2 ^ (prefixWord ++ tailWord_8151875).sum := by decide
  have hdescent : baseEnd_8151875 < baseStart_8151875 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151882 : List Nat := [3, 1, 2, 1, 1, 1, 2, 6, 1, 1, 4]
def baseStart_8151882 : Nat := 118140960795 + 8151882 * 2 ^ 59
def prefixEnd_8151882 : Nat := 4983230072969 + 3 ^ 40 * 8151882 * 2
def baseEnd_8151882 : Nat := 4185833704734979957885183

theorem tailTrace_8151882 : CollatzResearch.WordTrace tailWord_8151882 prefixEnd_8151882 4185833704734979957885183 := by
  unfold tailWord_8151882
  simp only [CollatzResearch.WordTrace]
  refine ⟨74330890663282804862392475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198215708435420812966379933 74330890663282804862392475)
  ·
    refine ⟨111496335994924207293588713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74330890663282804862392475 111496335994924207293588713)
    ·
      refine ⟨83622251996193155470191535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111496335994924207293588713 83622251996193155470191535)
      ·
        refine ⟨125433377994289733205287303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83622251996193155470191535 125433377994289733205287303)
        ·
          refine ⟨188150066991434599807930955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125433377994289733205287303 188150066991434599807930955)
          ·
            refine ⟨282225100487151899711896433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188150066991434599807930955 282225100487151899711896433)
            ·
              refine ⟨211668825365363924783922325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282225100487151899711896433 211668825365363924783922325)
              ·
                refine ⟨9921976189001433974246359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 211668825365363924783922325 9921976189001433974246359)
                ·
                  refine ⟨14882964283502150961369539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9921976189001433974246359 14882964283502150961369539)
                  ·
                    refine ⟨22324446425253226442054309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14882964283502150961369539 22324446425253226442054309)
                    ·
                      refine ⟨4185833704734979957885183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22324446425253226442054309 4185833704734979957885183)
                      ·
                        rfl

theorem cell23_8151882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 6, 1, 1, 4].length) (baseStart_8151882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151882 prefixEnd_8151882 := by exact prefixLift 8151882
  have htrace : WordTrace (prefixWord ++ tailWord_8151882) baseStart_8151882 baseEnd_8151882 := by
    simpa [prefixWord, tailWord_8151882, baseEnd_8151882] using wordTrace_append hprefix tailTrace_8151882
  have hstable : (prefixWord ++ tailWord_8151882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151882).length < 2 ^ (prefixWord ++ tailWord_8151882).sum := by decide
  have hdescent : baseEnd_8151882 < baseStart_8151882 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151926 : List Nat := [5, 1, 1, 3, 1, 1, 2, 3, 2, 4]
def baseStart_8151926 : Nat := 118140960795 + 8151926 * 2 ^ 59
def prefixEnd_8151926 : Nat := 4983230072969 + 3 ^ 40 * 8151926 * 2
def baseEnd_8151926 : Nat := 1395285432627925928578327

theorem tailTrace_8151926 : CollatzResearch.WordTrace tailWord_8151926 prefixEnd_8151926 1395285432627925928578327 := by
  unfold tailWord_8151926
  simp only [CollatzResearch.WordTrace]
  refine ⟨18582822966560738435260727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198216778309981209976114421 18582822966560738435260727)
  ·
    refine ⟨27874234449841107652891091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18582822966560738435260727 27874234449841107652891091)
    ·
      refine ⟨41811351674761661479336637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27874234449841107652891091 41811351674761661479336637)
      ·
        refine ⟨15679256878035623054751239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41811351674761661479336637 15679256878035623054751239)
        ·
          refine ⟨23518885317053434582126859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15679256878035623054751239 23518885317053434582126859)
          ·
            refine ⟨35278327975580151873190289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23518885317053434582126859 35278327975580151873190289)
            ·
              refine ⟨26458745981685113904892717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35278327975580151873190289 26458745981685113904892717)
              ·
                refine ⟨9922029743131917714334769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26458745981685113904892717 9922029743131917714334769)
                ·
                  refine ⟨7441522307348938285751077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9922029743131917714334769 7441522307348938285751077)
                  ·
                    refine ⟨1395285432627925928578327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7441522307348938285751077 1395285432627925928578327)
                    ·
                      rfl

theorem cell23_8151926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_8151926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151926 prefixEnd_8151926 := by exact prefixLift 8151926
  have htrace : WordTrace (prefixWord ++ tailWord_8151926) baseStart_8151926 baseEnd_8151926 := by
    simpa [prefixWord, tailWord_8151926, baseEnd_8151926] using wordTrace_append hprefix tailTrace_8151926
  have hstable : (prefixWord ++ tailWord_8151926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151926).length < 2 ^ (prefixWord ++ tailWord_8151926).sum := by decide
  have hdescent : baseEnd_8151926 < baseStart_8151926 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151955 : List Nat := [1, 1, 1, 2, 1, 2, 1, 4, 1, 5, 4]
def baseStart_8151955 : Nat := 118140960795 + 8151955 * 2 ^ 59
def prefixEnd_8151955 : Nat := 4983230072969 + 3 ^ 40 * 8151955 * 2
def baseEnd_8151955 : Nat := 4185871188822758172272347

theorem tailTrace_8151955 : CollatzResearch.WordTrace tailWord_8151955 prefixEnd_8151955 4185871188822758172272347 := by
  unfold tailWord_8151955
  simp only [CollatzResearch.WordTrace]
  refine ⟨297326225181866752916977319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198217483454577835277984879 297326225181866752916977319)
  ·
    refine ⟨445989337772800129375465979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297326225181866752916977319 445989337772800129375465979)
    ·
      refine ⟨668984006659200194063198969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445989337772800129375465979 668984006659200194063198969)
      ·
        refine ⟨501738004994400145547399227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 668984006659200194063198969 501738004994400145547399227)
        ·
          refine ⟨752607007491600218321098841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501738004994400145547399227 752607007491600218321098841)
          ·
            refine ⟨564455255618700163740824131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 752607007491600218321098841 564455255618700163740824131)
            ·
              refine ⟨846682883428050245611236197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 564455255618700163740824131 846682883428050245611236197)
              ·
                refine ⟨158753040642759421052106787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 846682883428050245611236197 158753040642759421052106787)
                ·
                  refine ⟨238129560964139131578160181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158753040642759421052106787 238129560964139131578160181)
                  ·
                    refine ⟨22324646340388043585452517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 238129560964139131578160181 22324646340388043585452517)
                    ·
                      refine ⟨4185871188822758172272347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22324646340388043585452517 4185871188822758172272347)
                      ·
                        rfl

theorem cell23_8151955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 5, 4].length) (baseStart_8151955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151955 prefixEnd_8151955 := by exact prefixLift 8151955
  have htrace : WordTrace (prefixWord ++ tailWord_8151955) baseStart_8151955 baseEnd_8151955 := by
    simpa [prefixWord, tailWord_8151955, baseEnd_8151955] using wordTrace_append hprefix tailTrace_8151955
  have hstable : (prefixWord ++ tailWord_8151955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151955).length < 2 ^ (prefixWord ++ tailWord_8151955).sum := by decide
  have hdescent : baseEnd_8151955 < baseStart_8151955 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8151990 : List Nat := [5, 1, 4, 1, 1, 2, 2, 7]
def baseStart_8151990 : Nat := 118140960795 + 8151990 * 2 ^ 59
def prefixEnd_8151990 : Nat := 4983230072969 + 3 ^ 40 * 8151990 * 2
def baseEnd_8151990 : Nat := 155032931875765390197581

theorem tailTrace_8151990 : CollatzResearch.WordTrace tailWord_8151990 prefixEnd_8151990 155032931875765390197581 := by
  unfold tailWord_8151990
  simp only [CollatzResearch.WordTrace]
  refine ⟨18582968858546247118406339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 198218334491159969263000949 18582968858546247118406339)
  ·
    refine ⟨27874453287819370677609509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18582968858546247118406339 27874453287819370677609509)
    ·
      refine ⟨5226459991466132002051783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27874453287819370677609509 5226459991466132002051783)
      ·
        refine ⟨7839689987199198003077675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5226459991466132002051783 7839689987199198003077675)
        ·
          refine ⟨11759534980798797004616513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7839689987199198003077675 11759534980798797004616513)
          ·
            refine ⟨8819651235599097753462385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11759534980798797004616513 8819651235599097753462385)
            ·
              refine ⟨6614738426699323315096789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8819651235599097753462385 6614738426699323315096789)
              ·
                refine ⟨155032931875765390197581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6614738426699323315096789 155032931875765390197581)
                ·
                  rfl

theorem cell23_8151990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 7].length) (baseStart_8151990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8151990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8151990 prefixEnd_8151990 := by exact prefixLift 8151990
  have htrace : WordTrace (prefixWord ++ tailWord_8151990) baseStart_8151990 baseEnd_8151990 := by
    simpa [prefixWord, tailWord_8151990, baseEnd_8151990] using wordTrace_append hprefix tailTrace_8151990
  have hstable : (prefixWord ++ tailWord_8151990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8151990).length < 2 ^ (prefixWord ++ tailWord_8151990).sum := by decide
  have hdescent : baseEnd_8151990 < baseStart_8151990 := by decide
  rcases family_descends (prefixWord ++ tailWord_8151990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8152029 : List Nat := [1, 4, 3, 1, 2, 1, 3, 1, 7]
def baseStart_8152029 : Nat := 118140960795 + 8152029 * 2 ^ 59
def prefixEnd_8152029 : Nat := 4983230072969 + 3 ^ 40 * 8152029 * 2
def baseEnd_8152029 : Nat := 465101020710132320305223

theorem tailTrace_8152029 : CollatzResearch.WordTrace tailWord_8152029 prefixEnd_8152029 465101020710132320305223 := by
  unfold tailWord_8152029
  simp only [CollatzResearch.WordTrace]
  refine ⟨297328924183598663555171141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198219282789065775703447427 297328924183598663555171141)
  ·
    refine ⟨55749173284424749416594589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 297328924183598663555171141 55749173284424749416594589)
    ·
      refine ⟨20905939981659281031222971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55749173284424749416594589 20905939981659281031222971)
      ·
        refine ⟨31358909972488921546834457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20905939981659281031222971 31358909972488921546834457)
        ·
          refine ⟨23519182479366691160125843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31358909972488921546834457 23519182479366691160125843)
          ·
            refine ⟨35278773719050036740188765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23519182479366691160125843 35278773719050036740188765)
            ·
              refine ⟨13229540144643763777570787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35278773719050036740188765 13229540144643763777570787)
              ·
                refine ⟨19844310216965645666356181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13229540144643763777570787 19844310216965645666356181)
                ·
                  refine ⟨465101020710132320305223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19844310216965645666356181 465101020710132320305223)
                  ·
                    rfl

theorem cell23_8152029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 7].length) (baseStart_8152029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8152029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8152029 prefixEnd_8152029 := by exact prefixLift 8152029
  have htrace : WordTrace (prefixWord ++ tailWord_8152029) baseStart_8152029 baseEnd_8152029 := by
    simpa [prefixWord, tailWord_8152029, baseEnd_8152029] using wordTrace_append hprefix tailTrace_8152029
  have hstable : (prefixWord ++ tailWord_8152029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8152029).length < 2 ^ (prefixWord ++ tailWord_8152029).sum := by decide
  have hdescent : baseEnd_8152029 < baseStart_8152029 := by decide
  rcases family_descends (prefixWord ++ tailWord_8152029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8152139 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 5, 5, 2]
def baseStart_8152139 : Nat := 118140960795 + 8152139 * 2 ^ 59
def prefixEnd_8152139 : Nat := 4983230072969 + 3 ^ 40 * 8152139 * 2
def baseEnd_8152139 : Nat := 4185965669263185452371501

theorem tailTrace_8152139 : CollatzResearch.WordTrace tailWord_8152139 prefixEnd_8152139 4185965669263185452371501 := by
  unfold tailWord_8152139
  simp only [CollatzResearch.WordTrace]
  refine ⟨297332936213200152341675471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198221957475466768227783647 297332936213200152341675471)
  ·
    refine ⟨445999404319800228512513207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297332936213200152341675471 445999404319800228512513207)
    ·
      refine ⟨668999106479700342768769811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 445999404319800228512513207 668999106479700342768769811)
      ·
        refine ⟨1003498659719550514153154717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 668999106479700342768769811 1003498659719550514153154717)
        ·
          refine ⟨376311997394831442807433019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1003498659719550514153154717 376311997394831442807433019)
          ·
            refine ⟨564467996092247164211149529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376311997394831442807433019 564467996092247164211149529)
            ·
              refine ⟨423350997069185373158362147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 564467996092247164211149529 423350997069185373158362147)
              ·
                refine ⟨635026495603778059737543221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 423350997069185373158362147 635026495603778059737543221)
                ·
                  refine ⟨59533733962854193100394677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 635026495603778059737543221 59533733962854193100394677)
                  ·
                    refine ⟨5581287559017580603162001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59533733962854193100394677 5581287559017580603162001)
                    ·
                      refine ⟨4185965669263185452371501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5581287559017580603162001 4185965669263185452371501)
                      ·
                        rfl

theorem cell23_8152139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 5, 2].length) (baseStart_8152139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8152139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8152139 prefixEnd_8152139 := by exact prefixLift 8152139
  have htrace : WordTrace (prefixWord ++ tailWord_8152139) baseStart_8152139 baseEnd_8152139 := by
    simpa [prefixWord, tailWord_8152139, baseEnd_8152139] using wordTrace_append hprefix tailTrace_8152139
  have hstable : (prefixWord ++ tailWord_8152139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8152139).length < 2 ^ (prefixWord ++ tailWord_8152139).sum := by decide
  have hdescent : baseEnd_8152139 < baseStart_8152139 := by decide
  rcases family_descends (prefixWord ++ tailWord_8152139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8152156 : List Nat := [2, 2, 4, 1, 1, 1, 1, 1, 3, 5, 2]
def baseStart_8152156 : Nat := 118140960795 + 8152156 * 2 ^ 59
def prefixEnd_8152156 : Nat := 4983230072969 + 3 ^ 40 * 8152156 * 2
def baseEnd_8152156 : Nat := 4185974398434311885858923

theorem tailTrace_8152156 : CollatzResearch.WordTrace tailWord_8152156 prefixEnd_8152156 4185974398434311885858923 := by
  unfold tailWord_8152156
  simp only [CollatzResearch.WordTrace]
  refine ⟨148666778127069282122522161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198222370836092376163362881 148666778127069282122522161)
  ·
    refine ⟨111500083595301961591891621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148666778127069282122522161 111500083595301961591891621)
    ·
      refine ⟨20906265674119117798479679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111500083595301961591891621 20906265674119117798479679)
      ·
        refine ⟨31359398511178676697719519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20906265674119117798479679 31359398511178676697719519)
        ·
          refine ⟨47039097766768015046579279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31359398511178676697719519 47039097766768015046579279)
          ·
            refine ⟨70558646650152022569868919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47039097766768015046579279 70558646650152022569868919)
            ·
              refine ⟨105837969975228033854803379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70558646650152022569868919 105837969975228033854803379)
              ·
                refine ⟨158756954962842050782205069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105837969975228033854803379 158756954962842050782205069)
                ·
                  refine ⟨59533858111065769043326901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158756954962842050782205069 59533858111065769043326901)
                  ·
                    refine ⟨5581299197912415847811897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59533858111065769043326901 5581299197912415847811897)
                    ·
                      refine ⟨4185974398434311885858923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5581299197912415847811897 4185974398434311885858923)
                      ·
                        rfl

theorem cell23_8152156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_8152156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8152156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8152156 prefixEnd_8152156 := by exact prefixLift 8152156
  have htrace : WordTrace (prefixWord ++ tailWord_8152156) baseStart_8152156 baseEnd_8152156 := by
    simpa [prefixWord, tailWord_8152156, baseEnd_8152156] using wordTrace_append hprefix tailTrace_8152156
  have hstable : (prefixWord ++ tailWord_8152156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8152156).length < 2 ^ (prefixWord ++ tailWord_8152156).sum := by decide
  have hdescent : baseEnd_8152156 < baseStart_8152156 := by decide
  rcases family_descends (prefixWord ++ tailWord_8152156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8152192 : List Nat := [2, 1, 1, 2, 1, 3, 13]
def baseStart_8152192 : Nat := 118140960795 + 8152192 * 2 ^ 59
def prefixEnd_8152192 : Nat := 4983230072969 + 3 ^ 40 * 8152192 * 2
def baseEnd_8152192 : Nat := 51678924490591033888997

theorem tailTrace_8152192 : CollatzResearch.WordTrace tailWord_8152192 prefixEnd_8152192 51678924490591033888997 := by
  unfold tailWord_8152192
  simp only [CollatzResearch.WordTrace]
  refine ⟨148667434641004071196677415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198223246188005428262236553 148667434641004071196677415)
  ·
    refine ⟨223001151961506106795016123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148667434641004071196677415 223001151961506106795016123)
    ·
      refine ⟨334501727942259160192524185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223001151961506106795016123 334501727942259160192524185)
      ·
        refine ⟨250876295956694370144393139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334501727942259160192524185 250876295956694370144393139)
        ·
          refine ⟨376314443935041555216589709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250876295956694370144393139 376314443935041555216589709)
          ·
            refine ⟨141117916475640583206221141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 376314443935041555216589709 141117916475640583206221141)
            ·
              refine ⟨51678924490591033888997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 141117916475640583206221141 51678924490591033888997)
              ·
                rfl

theorem cell23_8152192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 13].length) (baseStart_8152192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8152192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8152192 prefixEnd_8152192 := by exact prefixLift 8152192
  have htrace : WordTrace (prefixWord ++ tailWord_8152192) baseStart_8152192 baseEnd_8152192 := by
    simpa [prefixWord, tailWord_8152192, baseEnd_8152192] using wordTrace_append hprefix tailTrace_8152192
  have hstable : (prefixWord ++ tailWord_8152192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8152192).length < 2 ^ (prefixWord ++ tailWord_8152192).sum := by decide
  have hdescent : baseEnd_8152192 < baseStart_8152192 := by decide
  rcases family_descends (prefixWord ++ tailWord_8152192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8152196 : List Nat := [2, 3, 2, 1, 2, 2, 2, 1, 4, 4]
def baseStart_8152196 : Nat := 118140960795 + 8152196 * 2 ^ 59
def prefixEnd_8152196 : Nat := 4983230072969 + 3 ^ 40 * 8152196 * 2
def baseEnd_8152196 : Nat := 1395331645886830576452913

theorem tailTrace_8152196 : CollatzResearch.WordTrace tailWord_8152196 prefixEnd_8152196 1395331645886830576452913 := by
  unfold tailWord_8152196
  simp only [CollatzResearch.WordTrace]
  refine ⟨148667507586996825538250221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198223343449329100717666961 148667507586996825538250221)
  ·
    refine ⟨55750315345123809576843833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148667507586996825538250221 55750315345123809576843833)
    ·
      refine ⟨41812736508842857182632875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55750315345123809576843833 41812736508842857182632875)
      ·
        refine ⟨62719104763264285773949313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41812736508842857182632875 62719104763264285773949313)
        ·
          refine ⟨47039328572448214330461985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62719104763264285773949313 47039328572448214330461985)
          ·
            refine ⟨35279496429336160747846489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47039328572448214330461985 35279496429336160747846489)
            ·
              refine ⟨26459622322002120560884867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35279496429336160747846489 26459622322002120560884867)
              ·
                refine ⟨39689433483003180841327301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26459622322002120560884867 39689433483003180841327301)
                ·
                  refine ⟨7441768778063096407748869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39689433483003180841327301 7441768778063096407748869)
                  ·
                    refine ⟨1395331645886830576452913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7441768778063096407748869 1395331645886830576452913)
                    ·
                      rfl

theorem cell23_8152196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_8152196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8152196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8152196 prefixEnd_8152196 := by exact prefixLift 8152196
  have htrace : WordTrace (prefixWord ++ tailWord_8152196) baseStart_8152196 baseEnd_8152196 := by
    simpa [prefixWord, tailWord_8152196, baseEnd_8152196] using wordTrace_append hprefix tailTrace_8152196
  have hstable : (prefixWord ++ tailWord_8152196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8152196).length < 2 ^ (prefixWord ++ tailWord_8152196).sum := by decide
  have hdescent : baseEnd_8152196 < baseStart_8152196 := by decide
  rcases family_descends (prefixWord ++ tailWord_8152196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8152197 : List Nat := [1, 3, 1, 1, 6, 1, 3, 2, 1, 1, 3]
def baseStart_8152197 : Nat := 118140960795 + 8152197 * 2 ^ 59
def prefixEnd_8152197 : Nat := 4983230072969 + 3 ^ 40 * 8152197 * 2
def baseEnd_8152197 : Nat := 4185995451141146225446235

theorem tailTrace_8152197 : CollatzResearch.WordTrace tailWord_8152197 prefixEnd_8152197 4185995451141146225446235 := by
  unfold tailWord_8152197
  simp only [CollatzResearch.WordTrace]
  refine ⟨297335051646990028247286845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198223367764660018831524563 297335051646990028247286845)
  ·
    refine ⟨111500644367621260592732567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297335051646990028247286845 111500644367621260592732567)
    ·
      refine ⟨167250966551431890889098851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111500644367621260592732567 167250966551431890889098851)
      ·
        refine ⟨250876449827147836333648277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167250966551431890889098851 250876449827147836333648277)
        ·
          refine ⟨11759833585647554828139763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 250876449827147836333648277 11759833585647554828139763)
          ·
            refine ⟨17639750378471332242209645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11759833585647554828139763 17639750378471332242209645)
            ·
              refine ⟨6614906391926749590828617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17639750378471332242209645 6614906391926749590828617)
              ·
                refine ⟨4961179793945062193121463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6614906391926749590828617 4961179793945062193121463)
                ·
                  refine ⟨7441769690917593289682195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4961179793945062193121463 7441769690917593289682195)
                  ·
                    refine ⟨11162654536376389934523293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7441769690917593289682195 11162654536376389934523293)
                    ·
                      refine ⟨4185995451141146225446235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11162654536376389934523293 4185995451141146225446235)
                      ·
                        rfl

theorem cell23_8152197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 2, 1, 1, 3].length) (baseStart_8152197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8152197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8152197 prefixEnd_8152197 := by exact prefixLift 8152197
  have htrace : WordTrace (prefixWord ++ tailWord_8152197) baseStart_8152197 baseEnd_8152197 := by
    simpa [prefixWord, tailWord_8152197, baseEnd_8152197] using wordTrace_append hprefix tailTrace_8152197
  have hstable : (prefixWord ++ tailWord_8152197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8152197).length < 2 ^ (prefixWord ++ tailWord_8152197).sum := by decide
  have hdescent : baseEnd_8152197 < baseStart_8152197 := by decide
  rcases family_descends (prefixWord ++ tailWord_8152197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8152206 : List Nat := [4, 1, 1, 3, 2, 1, 2, 2, 1, 1, 5]
def baseStart_8152206 : Nat := 118140960795 + 8152206 * 2 ^ 59
def prefixEnd_8152206 : Nat := 4983230072969 + 3 ^ 40 * 8152206 * 2
def baseEnd_8152206 : Nat := 4186000072467036690233693

theorem tailTrace_8152206 : CollatzResearch.WordTrace tailWord_8152206 prefixEnd_8152206 4186000072467036690233693 := by
  unfold tailWord_8152206
  simp only [CollatzResearch.WordTrace]
  refine ⟨37166922487994677848045559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198223586602638281856242981 37166922487994677848045559)
  ·
    refine ⟨55750383731992016772068339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37166922487994677848045559 55750383731992016772068339)
    ·
      refine ⟨83625575597988025158102509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55750383731992016772068339 83625575597988025158102509)
      ·
        refine ⟨31359590849245509434288441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83625575597988025158102509 31359590849245509434288441)
        ·
          refine ⟨23519693136934132075716331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31359590849245509434288441 23519693136934132075716331)
          ·
            refine ⟨35279539705401198113574497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23519693136934132075716331 35279539705401198113574497)
            ·
              refine ⟨26459654779050898585180873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35279539705401198113574497 26459654779050898585180873)
              ·
                refine ⟨19844741084288173938885655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26459654779050898585180873 19844741084288173938885655)
                ·
                  refine ⟨29767111626432260908328483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19844741084288173938885655 29767111626432260908328483)
                  ·
                    refine ⟨44650667439648391362492725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29767111626432260908328483 44650667439648391362492725)
                    ·
                      refine ⟨4186000072467036690233693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44650667439648391362492725 4186000072467036690233693)
                      ·
                        rfl

theorem cell23_8152206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_8152206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8152206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8152206 prefixEnd_8152206 := by exact prefixLift 8152206
  have htrace : WordTrace (prefixWord ++ tailWord_8152206) baseStart_8152206 baseEnd_8152206 := by
    simpa [prefixWord, tailWord_8152206, baseEnd_8152206] using wordTrace_append hprefix tailTrace_8152206
  have hstable : (prefixWord ++ tailWord_8152206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8152206).length < 2 ^ (prefixWord ++ tailWord_8152206).sum := by decide
  have hdescent : baseEnd_8152206 < baseStart_8152206 := by decide
  rcases family_descends (prefixWord ++ tailWord_8152206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8152223 : List Nat := [1, 1, 2, 6, 2, 1, 1, 1, 3, 2, 3]
def baseStart_8152223 : Nat := 118140960795 + 8152223 * 2 ^ 59
def prefixEnd_8152223 : Nat := 4983230072969 + 3 ^ 40 * 8152223 * 2
def baseEnd_8152223 : Nat := 4186008801638163123721115

theorem tailTrace_8152223 : CollatzResearch.WordTrace tailWord_8152223 prefixEnd_8152223 4186008801638163123721115 := by
  unfold tailWord_8152223
  simp only [CollatzResearch.WordTrace]
  refine ⟨297335999944895834687733323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198223999963263889791822215 297335999944895834687733323)
  ·
    refine ⟨446003999917343752031599985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297335999944895834687733323 446003999917343752031599985)
    ·
      refine ⟨334502999938007814023699989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446003999917343752031599985 334502999938007814023699989)
      ·
        refine ⟨15679828122094116282360937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 334502999938007814023699989 15679828122094116282360937)
        ·
          refine ⟨11759871091570587211770703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15679828122094116282360937 11759871091570587211770703)
          ·
            refine ⟨17639806637355880817656055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11759871091570587211770703 17639806637355880817656055)
            ·
              refine ⟨26459709956033821226484083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17639806637355880817656055 26459709956033821226484083)
              ·
                refine ⟨39689564934050731839726125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26459709956033821226484083 39689564934050731839726125)
                ·
                  refine ⟨14883586850269024439897297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39689564934050731839726125 14883586850269024439897297)
                  ·
                    refine ⟨11162690137701768329922973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14883586850269024439897297 11162690137701768329922973)
                    ·
                      refine ⟨4186008801638163123721115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11162690137701768329922973 4186008801638163123721115)
                      ·
                        rfl

theorem cell23_8152223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_8152223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8152223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8152223 prefixEnd_8152223 := by exact prefixLift 8152223
  have htrace : WordTrace (prefixWord ++ tailWord_8152223) baseStart_8152223 baseEnd_8152223 := by
    simpa [prefixWord, tailWord_8152223, baseEnd_8152223] using wordTrace_append hprefix tailTrace_8152223
  have hstable : (prefixWord ++ tailWord_8152223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8152223).length < 2 ^ (prefixWord ++ tailWord_8152223).sum := by decide
  have hdescent : baseEnd_8152223 < baseStart_8152223 := by decide
  rcases family_descends (prefixWord ++ tailWord_8152223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8152236 : List Nat := [2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 3]
def baseStart_8152236 : Nat := 118140960795 + 8152236 * 2 ^ 59
def prefixEnd_8152236 : Nat := 4983230072969 + 3 ^ 40 * 8152236 * 2
def baseEnd_8152236 : Nat := 4186015476886671572858555

theorem tailTrace_8152236 : CollatzResearch.WordTrace tailWord_8152236 prefixEnd_8152236 4186015476886671572858555 := by
  unfold tailWord_8152236
  simp only [CollatzResearch.WordTrace]
  refine ⟨148668237046924368953978281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198224316062565825271971041 148668237046924368953978281)
  ·
    refine ⟨111501177785193276715483711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148668237046924368953978281 111501177785193276715483711)
    ·
      refine ⟨167251766677789915073225567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111501177785193276715483711 167251766677789915073225567)
      ·
        refine ⟨250877650016684872609838351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167251766677789915073225567 250877650016684872609838351)
        ·
          refine ⟨376316475025027308914757527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250877650016684872609838351 376316475025027308914757527)
          ·
            refine ⟨564474712537540963372136291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376316475025027308914757527 564474712537540963372136291)
            ·
              refine ⟨846712068806311445058204437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 564474712537540963372136291 846712068806311445058204437)
              ·
                refine ⟨39689628225295848987103333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 846712068806311445058204437 39689628225295848987103333)
                ·
                  refine ⟨7441805292242971685081875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39689628225295848987103333 7441805292242971685081875)
                  ·
                    refine ⟨11162707938364457527622813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7441805292242971685081875 11162707938364457527622813)
                    ·
                      refine ⟨4186015476886671572858555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11162707938364457527622813 4186015476886671572858555)
                      ·
                        rfl

theorem cell23_8152236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 3].length) (baseStart_8152236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8152236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8152236 prefixEnd_8152236 := by exact prefixLift 8152236
  have htrace : WordTrace (prefixWord ++ tailWord_8152236) baseStart_8152236 baseEnd_8152236 := by
    simpa [prefixWord, tailWord_8152236, baseEnd_8152236] using wordTrace_append hprefix tailTrace_8152236
  have hstable : (prefixWord ++ tailWord_8152236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8152236).length < 2 ^ (prefixWord ++ tailWord_8152236).sum := by decide
  have hdescent : baseEnd_8152236 < baseStart_8152236 := by decide
  rcases family_descends (prefixWord ++ tailWord_8152236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8152253 : List Nat := [1, 4, 1, 2, 1, 1, 3, 4, 2, 1, 3]
def baseStart_8152253 : Nat := 118140960795 + 8152253 * 2 ^ 59
def prefixEnd_8152253 : Nat := 4983230072969 + 3 ^ 40 * 8152253 * 2
def baseEnd_8152253 : Nat := 4186024206057798006345977

theorem tailTrace_8152253 : CollatzResearch.WordTrace tailWord_8152253 prefixEnd_8152253 4186024206057798006345977 := by
  unfold tailWord_8152253
  simp only [CollatzResearch.WordTrace]
  refine ⟨297337094134787149811325413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198224729423191433207550275 297337094134787149811325413)
  ·
    refine ⟨55750705150272590589623515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 297337094134787149811325413 55750705150272590589623515)
    ·
      refine ⟨83626057725408885884435273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55750705150272590589623515 83626057725408885884435273)
      ·
        refine ⟨62719543294056664413326455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83626057725408885884435273 62719543294056664413326455)
        ·
          refine ⟨94079314941084996619989683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62719543294056664413326455 94079314941084996619989683)
          ·
            refine ⟨141118972411627494929984525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94079314941084996619989683 141118972411627494929984525)
            ·
              refine ⟨52919614654360310598744197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141118972411627494929984525 52919614654360310598744197)
              ·
                refine ⟨9922427747692558237264537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52919614654360310598744197 9922427747692558237264537)
                ·
                  refine ⟨7441820810769418677948403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9922427747692558237264537 7441820810769418677948403)
                  ·
                    refine ⟨11162731216154128016922605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7441820810769418677948403 11162731216154128016922605)
                    ·
                      refine ⟨4186024206057798006345977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11162731216154128016922605 4186024206057798006345977)
                      ·
                        rfl

theorem cell23_8152253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_8152253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8152253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8152253 prefixEnd_8152253 := by exact prefixLift 8152253
  have htrace : WordTrace (prefixWord ++ tailWord_8152253) baseStart_8152253 baseEnd_8152253 := by
    simpa [prefixWord, tailWord_8152253, baseEnd_8152253] using wordTrace_append hprefix tailTrace_8152253
  have hstable : (prefixWord ++ tailWord_8152253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8152253).length < 2 ^ (prefixWord ++ tailWord_8152253).sum := by decide
  have hdescent : baseEnd_8152253 < baseStart_8152253 := by decide
  rcases family_descends (prefixWord ++ tailWord_8152253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8152254 : List Nat := [4, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2]
def baseStart_8152254 : Nat := 118140960795 + 8152254 * 2 ^ 59
def prefixEnd_8152254 : Nat := 4983230072969 + 3 ^ 40 * 8152254 * 2
def baseEnd_8152254 : Nat := 4186024719538452502433473

theorem tailTrace_8152254 : CollatzResearch.WordTrace tailWord_8152254 prefixEnd_8152254 4186024719538452502433473 := by
  unfold tailWord_8152254
  simp only [CollatzResearch.WordTrace]
  refine ⟨37167141325972940872763977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198224753738522351321407877 37167141325972940872763977)
  ·
    refine ⟨27875355994479705654572983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37167141325972940872763977 27875355994479705654572983)
    ·
      refine ⟨41813033991719558481859475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27875355994479705654572983 41813033991719558481859475)
      ·
        refine ⟨62719550987579337722789213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41813033991719558481859475 62719550987579337722789213)
        ·
          refine ⟨23519831620342251646045955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62719550987579337722789213 23519831620342251646045955)
          ·
            refine ⟨35279747430513377469068933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23519831620342251646045955 35279747430513377469068933)
            ·
              refine ⟨6614952643221258275450425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35279747430513377469068933 6614952643221258275450425)
              ·
                refine ⟨4961214482415943706587819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6614952643221258275450425 4961214482415943706587819)
                ·
                  refine ⟨7441821723623915559881729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4961214482415943706587819 7441821723623915559881729)
                  ·
                    refine ⟨5581366292717936669911297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7441821723623915559881729 5581366292717936669911297)
                    ·
                      refine ⟨4186024719538452502433473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5581366292717936669911297 4186024719538452502433473)
                      ·
                        rfl

theorem cell23_8152254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2].length) (baseStart_8152254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8152254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8152254 prefixEnd_8152254 := by exact prefixLift 8152254
  have htrace : WordTrace (prefixWord ++ tailWord_8152254) baseStart_8152254 baseEnd_8152254 := by
    simpa [prefixWord, tailWord_8152254, baseEnd_8152254] using wordTrace_append hprefix tailTrace_8152254
  have hstable : (prefixWord ++ tailWord_8152254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8152254).length < 2 ^ (prefixWord ++ tailWord_8152254).sum := by decide
  have hdescent : baseEnd_8152254 < baseStart_8152254 := by decide
  rcases family_descends (prefixWord ++ tailWord_8152254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8152279 : List Nat := [1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 5]
def baseStart_8152279 : Nat := 118140960795 + 8152279 * 2 ^ 59
def prefixEnd_8152279 : Nat := 4983230072969 + 3 ^ 40 * 8152279 * 2
def baseEnd_8152279 : Nat := 4186037556554814904620857

theorem tailTrace_8152279 : CollatzResearch.WordTrace tailWord_8152279 prefixEnd_8152279 4186037556554814904620857 := by
  unfold tailWord_8152279
  simp only [CollatzResearch.WordTrace]
  refine ⟨297338042432692956251771891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198225361621795304167847927 297338042432692956251771891)
  ·
    refine ⟨446007063649039434377657837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297338042432692956251771891 446007063649039434377657837)
    ·
      refine ⟨167252648868389787891621689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 446007063649039434377657837 167252648868389787891621689)
      ·
        refine ⟨125439486651292340918716267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167252648868389787891621689 125439486651292340918716267)
        ·
          refine ⟨188159229976938511378074401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125439486651292340918716267 188159229976938511378074401)
          ·
            refine ⟨141119422482703883533555801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188159229976938511378074401 141119422482703883533555801)
            ·
              refine ⟨105839566862027912650166851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141119422482703883533555801 105839566862027912650166851)
              ·
                refine ⟨158759350293041868975250277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105839566862027912650166851 158759350293041868975250277)
                ·
                  refine ⟨29767378179945350432859427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158759350293041868975250277 29767378179945350432859427)
                  ·
                    refine ⟨44651067269918025649289141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29767378179945350432859427 44651067269918025649289141)
                    ·
                      refine ⟨4186037556554814904620857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44651067269918025649289141 4186037556554814904620857)
                      ·
                        rfl

theorem cell23_8152279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_8152279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8152279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8152279 prefixEnd_8152279 := by exact prefixLift 8152279
  have htrace : WordTrace (prefixWord ++ tailWord_8152279) baseStart_8152279 baseEnd_8152279 := by
    simpa [prefixWord, tailWord_8152279, baseEnd_8152279] using wordTrace_append hprefix tailTrace_8152279
  have hstable : (prefixWord ++ tailWord_8152279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8152279).length < 2 ^ (prefixWord ++ tailWord_8152279).sum := by decide
  have hdescent : baseEnd_8152279 < baseStart_8152279 := by decide
  rcases family_descends (prefixWord ++ tailWord_8152279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8152329 : List Nat := [1, 2, 1, 1, 3, 3, 1, 1, 3, 7]
def baseStart_8152329 : Nat := 118140960795 + 8152329 * 2 ^ 59
def prefixEnd_8152329 : Nat := 4983230072969 + 3 ^ 40 * 8152329 * 2
def baseEnd_8152329 : Nat := 1395354410195846569665209

theorem tailTrace_8152329 : CollatzResearch.WordTrace tailWord_8152329 prefixEnd_8152329 1395354410195846569665209 := by
  unfold tailWord_8152329
  simp only [CollatzResearch.WordTrace]
  refine ⟨297339866082511814791092041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198226577388341209860728027 297339866082511814791092041)
  ·
    refine ⟨223004899561883861093319031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297339866082511814791092041 223004899561883861093319031)
    ·
      refine ⟨334507349342825791639978547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223004899561883861093319031 334507349342825791639978547)
      ·
        refine ⟨501761024014238687459967821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334507349342825791639978547 501761024014238687459967821)
        ·
          refine ⟨188160384005339507797487933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 501761024014238687459967821 188160384005339507797487933)
          ·
            refine ⟨70560144002002315424057975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188160384005339507797487933 70560144002002315424057975)
            ·
              refine ⟨105840216003003473136086963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70560144002002315424057975 105840216003003473136086963)
              ·
                refine ⟨158760324004505209704130445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105840216003003473136086963 158760324004505209704130445)
                ·
                  refine ⟨59535121501689453639048917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158760324004505209704130445 59535121501689453639048917)
                  ·
                    refine ⟨1395354410195846569665209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59535121501689453639048917 1395354410195846569665209)
                    ·
                      rfl

theorem cell23_8152329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 7].length) (baseStart_8152329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8152329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8152329 prefixEnd_8152329 := by exact prefixLift 8152329
  have htrace : WordTrace (prefixWord ++ tailWord_8152329) baseStart_8152329 baseEnd_8152329 := by
    simpa [prefixWord, tailWord_8152329, baseEnd_8152329] using wordTrace_append hprefix tailTrace_8152329
  have hstable : (prefixWord ++ tailWord_8152329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8152329).length < 2 ^ (prefixWord ++ tailWord_8152329).sum := by decide
  have hdescent : baseEnd_8152329 < baseStart_8152329 := by decide
  rcases family_descends (prefixWord ++ tailWord_8152329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8152336 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 5, 7, 2]
def baseStart_8152336 : Nat := 118140960795 + 8152336 * 2 ^ 59
def prefixEnd_8152336 : Nat := 4983230072969 + 3 ^ 40 * 8152336 * 2
def baseEnd_8152336 : Nat := 4186066824952121181608095

theorem tailTrace_8152336 : CollatzResearch.WordTrace tailWord_8152336 prefixEnd_8152336 4186066824952121181608095 := by
  unfold tailWord_8152336
  simp only [CollatzResearch.WordTrace]
  refine ⟨148670060696743227493298431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198226747595657636657731241 148670060696743227493298431)
  ·
    refine ⟨223005091045114841239947647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148670060696743227493298431 223005091045114841239947647)
    ·
      refine ⟨334507636567672261859921471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223005091045114841239947647 334507636567672261859921471)
      ·
        refine ⟨501761454851508392789882207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334507636567672261859921471 501761454851508392789882207)
        ·
          refine ⟨752642182277262589184823311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501761454851508392789882207 752642182277262589184823311)
          ·
            refine ⟨1128963273415893883777234967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 752642182277262589184823311 1128963273415893883777234967)
            ·
              refine ⟨1693444910123840825665852451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1128963273415893883777234967 1693444910123840825665852451)
              ·
                refine ⟨2540167365185761238498778677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1693444910123840825665852451 2540167365185761238498778677)
                ·
                  refine ⟨238140690486165116109260501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2540167365185761238498778677 238140690486165116109260501)
                  ·
                    refine ⟨5581422433269494908810793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 238140690486165116109260501 5581422433269494908810793)
                    ·
                      refine ⟨4186066824952121181608095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5581422433269494908810793 4186066824952121181608095)
                      ·
                        rfl

theorem cell23_8152336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 5, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 5, 7, 2].length) (baseStart_8152336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8152336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8152336 prefixEnd_8152336 := by exact prefixLift 8152336
  have htrace : WordTrace (prefixWord ++ tailWord_8152336) baseStart_8152336 baseEnd_8152336 := by
    simpa [prefixWord, tailWord_8152336, baseEnd_8152336] using wordTrace_append hprefix tailTrace_8152336
  have hstable : (prefixWord ++ tailWord_8152336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8152336).length < 2 ^ (prefixWord ++ tailWord_8152336).sum := by decide
  have hdescent : baseEnd_8152336 < baseStart_8152336 := by decide
  rcases family_descends (prefixWord ++ tailWord_8152336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8152339 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 5]
def baseStart_8152339 : Nat := 118140960795 + 8152339 * 2 ^ 59
def prefixEnd_8152339 : Nat := 4983230072969 + 3 ^ 40 * 8152339 * 2
def baseEnd_8152339 : Nat := 4186068365394084669870581

theorem tailTrace_8152339 : CollatzResearch.WordTrace tailWord_8152339 prefixEnd_8152339 4186068365394084669870581 := by
  unfold tailWord_8152339
  simp only [CollatzResearch.WordTrace]
  refine ⟨297340230812475586498956071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198226820541650390999304047 297340230812475586498956071)
  ·
    refine ⟨446010346218713379748434107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297340230812475586498956071 446010346218713379748434107)
    ·
      refine ⟨669015519328070069622651161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446010346218713379748434107 669015519328070069622651161)
      ·
        refine ⟨501761639496052552216988371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 669015519328070069622651161 501761639496052552216988371)
        ·
          refine ⟨752642459244078828325482557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501761639496052552216988371 752642459244078828325482557)
          ·
            refine ⟨282240922216529560622055959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 752642459244078828325482557 282240922216529560622055959)
            ·
              refine ⟨423361383324794340933083939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282240922216529560622055959 423361383324794340933083939)
              ·
                refine ⟨635042074987191511399625909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 423361383324794340933083939 635042074987191511399625909)
                ·
                  refine ⟨59535194530049204193714929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 635042074987191511399625909 59535194530049204193714929)
                  ·
                    refine ⟨44651395897536903145286197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59535194530049204193714929 44651395897536903145286197)
                    ·
                      refine ⟨4186068365394084669870581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44651395897536903145286197 4186068365394084669870581)
                      ·
                        rfl

theorem cell23_8152339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 5].length) (baseStart_8152339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8152339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8152339 prefixEnd_8152339 := by exact prefixLift 8152339
  have htrace : WordTrace (prefixWord ++ tailWord_8152339) baseStart_8152339 baseEnd_8152339 := by
    simpa [prefixWord, tailWord_8152339, baseEnd_8152339] using wordTrace_append hprefix tailTrace_8152339
  have hstable : (prefixWord ++ tailWord_8152339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8152339).length < 2 ^ (prefixWord ++ tailWord_8152339).sum := by decide
  have hdescent : baseEnd_8152339 < baseStart_8152339 := by decide
  rcases family_descends (prefixWord ++ tailWord_8152339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8152346 : List Nat := [3, 1, 1, 3, 3, 1, 2, 1, 1, 7]
def baseStart_8152346 : Nat := 118140960795 + 8152346 * 2 ^ 59
def prefixEnd_8152346 : Nat := 4983230072969 + 3 ^ 40 * 8152346 * 2
def baseEnd_8152346 : Nat := 1395357319919555380827683

theorem tailTrace_8152346 : CollatzResearch.WordTrace tailWord_8152346 prefixEnd_8152346 1395357319919555380827683 := by
  unfold tailWord_8152346
  simp only [CollatzResearch.WordTrace]
  refine ⟨74335121530862556673615223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198226990748966817796307261 74335121530862556673615223)
  ·
    refine ⟨111502682296293835010422835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74335121530862556673615223 111502682296293835010422835)
    ·
      refine ⟨167254023444440752515634253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111502682296293835010422835 167254023444440752515634253)
      ·
        refine ⟨62720258791665282193362845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167254023444440752515634253 62720258791665282193362845)
        ·
          refine ⟨23520097046874480822511067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62720258791665282193362845 23520097046874480822511067)
          ·
            refine ⟨35280145570311721233766601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23520097046874480822511067 35280145570311721233766601)
            ·
              refine ⟨26460109177733790925324951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35280145570311721233766601 26460109177733790925324951)
              ·
                refine ⟨39690163766600686387987427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26460109177733790925324951 39690163766600686387987427)
                ·
                  refine ⟨59535245649901029581981141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39690163766600686387987427 59535245649901029581981141)
                  ·
                    refine ⟨1395357319919555380827683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59535245649901029581981141 1395357319919555380827683)
                    ·
                      rfl

theorem cell23_8152346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 1, 7].length) (baseStart_8152346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8152346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8152346 prefixEnd_8152346 := by exact prefixLift 8152346
  have htrace : WordTrace (prefixWord ++ tailWord_8152346) baseStart_8152346 baseEnd_8152346 := by
    simpa [prefixWord, tailWord_8152346, baseEnd_8152346] using wordTrace_append hprefix tailTrace_8152346
  have hstable : (prefixWord ++ tailWord_8152346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8152346).length < 2 ^ (prefixWord ++ tailWord_8152346).sum := by decide
  have hdescent : baseEnd_8152346 < baseStart_8152346 := by decide
  rcases family_descends (prefixWord ++ tailWord_8152346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8152356 : List Nat := [2, 3, 1, 3, 1, 1, 2, 2, 1, 2, 5]
def baseStart_8152356 : Nat := 118140960795 + 8152356 * 2 ^ 59
def prefixEnd_8152356 : Nat := 4983230072969 + 3 ^ 40 * 8152356 * 2
def baseEnd_8152356 : Nat := 4186077094565211103358003

theorem tailTrace_8152356 : CollatzResearch.WordTrace tailWord_8152356 prefixEnd_8152356 4186077094565211103358003 := by
  unfold tailWord_8152356
  simp only [CollatzResearch.WordTrace]
  refine ⟨148670425426706999201162461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198227233902275998934883281 148670425426706999201162461)
  ·
    refine ⟨55751409535015124700435923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148670425426706999201162461 55751409535015124700435923)
    ·
      refine ⟨83627114302522687050653885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55751409535015124700435923 83627114302522687050653885)
      ·
        refine ⟨31360167863446007643995207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83627114302522687050653885 31360167863446007643995207)
        ·
          refine ⟨47040251795169011465992811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31360167863446007643995207 47040251795169011465992811)
          ·
            refine ⟨70560377692753517198989217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47040251795169011465992811 70560377692753517198989217)
            ·
              refine ⟨52920283269565137899241913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70560377692753517198989217 52920283269565137899241913)
              ·
                refine ⟨39690212452173853424431435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52920283269565137899241913 39690212452173853424431435)
                ·
                  refine ⟨59535318678260780136647153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39690212452173853424431435 59535318678260780136647153)
                  ·
                    refine ⟨44651489008695585102485365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59535318678260780136647153 44651489008695585102485365)
                    ·
                      refine ⟨4186077094565211103358003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44651489008695585102485365 4186077094565211103358003)
                      ·
                        rfl

theorem cell23_8152356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_8152356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8152356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8152356 prefixEnd_8152356 := by exact prefixLift 8152356
  have htrace : WordTrace (prefixWord ++ tailWord_8152356) baseStart_8152356 baseEnd_8152356 := by
    simpa [prefixWord, tailWord_8152356, baseEnd_8152356] using wordTrace_append hprefix tailTrace_8152356
  have hstable : (prefixWord ++ tailWord_8152356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8152356).length < 2 ^ (prefixWord ++ tailWord_8152356).sum := by decide
  have hdescent : baseEnd_8152356 < baseStart_8152356 := by decide
  rcases family_descends (prefixWord ++ tailWord_8152356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8152379 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 6]
def baseStart_8152379 : Nat := 118140960795 + 8152379 * 2 ^ 59
def prefixEnd_8152379 : Nat := 4983230072969 + 3 ^ 40 * 8152379 * 2
def baseEnd_8152379 : Nat := 4186088904620264513370397

theorem tailTrace_8152379 : CollatzResearch.WordTrace tailWord_8152379 prefixEnd_8152379 4186088904620264513370397 := by
  unfold tailWord_8152379
  simp only [CollatzResearch.WordTrace]
  refine ⟨297341689732330673330412191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198227793154887115553608127 297341689732330673330412191)
  ·
    refine ⟨446012534598496009995618287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297341689732330673330412191 446012534598496009995618287)
    ·
      refine ⟨669018801897744014993427431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446012534598496009995618287 669018801897744014993427431)
      ·
        refine ⟨1003528202846616022490141147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 669018801897744014993427431 1003528202846616022490141147)
        ·
          refine ⟨1505292304269924033735211721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1003528202846616022490141147 1505292304269924033735211721)
          ·
            refine ⟨1128969228202443025301408791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1505292304269924033735211721 1128969228202443025301408791)
            ·
              refine ⟨1693453842303664537952113187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1128969228202443025301408791 1693453842303664537952113187)
              ·
                refine ⟨2540180763455496806928169781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1693453842303664537952113187 2540180763455496806928169781)
                ·
                  refine ⟨238141946573952825649515917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2540180763455496806928169781 238141946573952825649515917)
                  ·
                    refine ⟨89303229965232309618568469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 238141946573952825649515917 89303229965232309618568469)
                    ·
                      refine ⟨4186088904620264513370397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89303229965232309618568469 4186088904620264513370397)
                      ·
                        rfl

theorem cell23_8152379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 6].length) (baseStart_8152379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8152379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8152379 prefixEnd_8152379 := by exact prefixLift 8152379
  have htrace : WordTrace (prefixWord ++ tailWord_8152379) baseStart_8152379 baseEnd_8152379 := by
    simpa [prefixWord, tailWord_8152379, baseEnd_8152379] using wordTrace_append hprefix tailTrace_8152379
  have hstable : (prefixWord ++ tailWord_8152379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8152379).length < 2 ^ (prefixWord ++ tailWord_8152379).sum := by decide
  have hdescent : baseEnd_8152379 < baseStart_8152379 := by decide
  rcases family_descends (prefixWord ++ tailWord_8152379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8152397 : List Nat := [1, 6, 1, 3, 1, 1, 2, 1, 2, 5]
def baseStart_8152397 : Nat := 118140960795 + 8152397 * 2 ^ 59
def prefixEnd_8152397 : Nat := 4983230072969 + 3 ^ 40 * 8152397 * 2
def baseEnd_8152397 : Nat := 1395366049090681814315105

theorem tailTrace_8152397 : CollatzResearch.WordTrace tailWord_8152397 prefixEnd_8152397 1395366049090681814315105 := by
  unfold tailWord_8152397
  simp only [CollatzResearch.WordTrace]
  refine ⟨297342346246265462404567445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198228230830843641603044963 297342346246265462404567445)
  ·
    refine ⟨13937922480293693550214099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 297342346246265462404567445 13937922480293693550214099)
    ·
      refine ⟨20906883720440540325321149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13937922480293693550214099 20906883720440540325321149)
      ·
        refine ⟨7840081395165202621995431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20906883720440540325321149 7840081395165202621995431)
        ·
          refine ⟨11760122092747803932993147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7840081395165202621995431 11760122092747803932993147)
          ·
            refine ⟨17640183139121705899489721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11760122092747803932993147 17640183139121705899489721)
            ·
              refine ⟨13230137354341279424617291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17640183139121705899489721 13230137354341279424617291)
              ·
                refine ⟨19845206031511919136925937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13230137354341279424617291 19845206031511919136925937)
                ·
                  refine ⟨14883904523633939352694453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19845206031511919136925937 14883904523633939352694453)
                  ·
                    refine ⟨1395366049090681814315105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14883904523633939352694453 1395366049090681814315105)
                    ·
                      rfl

theorem cell23_8152397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_8152397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8152397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8152397 prefixEnd_8152397 := by exact prefixLift 8152397
  have htrace : WordTrace (prefixWord ++ tailWord_8152397) baseStart_8152397 baseEnd_8152397 := by
    simpa [prefixWord, tailWord_8152397, baseEnd_8152397] using wordTrace_append hprefix tailTrace_8152397
  have hstable : (prefixWord ++ tailWord_8152397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8152397).length < 2 ^ (prefixWord ++ tailWord_8152397).sum := by decide
  have hdescent : baseEnd_8152397 < baseStart_8152397 := by decide
  rcases family_descends (prefixWord ++ tailWord_8152397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8152403 : List Nat := [1, 1, 1, 2, 1, 1, 8, 1, 2, 2, 3]
def baseStart_8152403 : Nat := 118140960795 + 8152403 * 2 ^ 59
def prefixEnd_8152403 : Nat := 4983230072969 + 3 ^ 40 * 8152403 * 2
def baseEnd_8152403 : Nat := 4186101228155972419470287

theorem tailTrace_8152403 : CollatzResearch.WordTrace tailWord_8152403 prefixEnd_8152403 4186101228155972419470287 := by
  unfold tailWord_8152403
  simp only [CollatzResearch.WordTrace]
  refine ⟨297342565084243725429285863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198228376722829150286190575 297342565084243725429285863)
  ·
    refine ⟨446013847626365588143928795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297342565084243725429285863 446013847626365588143928795)
    ·
      refine ⟨669020771439548382215893193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446013847626365588143928795 669020771439548382215893193)
      ·
        refine ⟨501765578579661286661919895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 669020771439548382215893193 501765578579661286661919895)
        ·
          refine ⟨752648367869491929992879843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501765578579661286661919895 752648367869491929992879843)
          ·
            refine ⟨1128972551804237894989319765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 752648367869491929992879843 1128972551804237894989319765)
            ·
              refine ⟨13230147091455912831906091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1128972551804237894989319765 13230147091455912831906091)
              ·
                refine ⟨19845220637183869247859137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13230147091455912831906091 19845220637183869247859137)
                ·
                  refine ⟨14883915477887901935894353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19845220637183869247859137 14883915477887901935894353)
                  ·
                    refine ⟨11162936608415926451920765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14883915477887901935894353 11162936608415926451920765)
                    ·
                      refine ⟨4186101228155972419470287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11162936608415926451920765 4186101228155972419470287)
                      ·
                        rfl

theorem cell23_8152403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 2, 2, 3].length) (baseStart_8152403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8152403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8152403 prefixEnd_8152403 := by exact prefixLift 8152403
  have htrace : WordTrace (prefixWord ++ tailWord_8152403) baseStart_8152403 baseEnd_8152403 := by
    simpa [prefixWord, tailWord_8152403, baseEnd_8152403] using wordTrace_append hprefix tailTrace_8152403
  have hstable : (prefixWord ++ tailWord_8152403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8152403).length < 2 ^ (prefixWord ++ tailWord_8152403).sum := by decide
  have hdescent : baseEnd_8152403 < baseStart_8152403 := by decide
  rcases family_descends (prefixWord ++ tailWord_8152403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8152443 : List Nat := [1, 1, 1, 1, 1, 6, 2, 2, 1, 5, 2]
def baseStart_8152443 : Nat := 118140960795 + 8152443 * 2 ^ 59
def prefixEnd_8152443 : Nat := 4983230072969 + 3 ^ 40 * 8152443 * 2
def baseEnd_8152443 : Nat := 4186121767382152262970103

theorem tailTrace_8152443 : CollatzResearch.WordTrace tailWord_8152443 prefixEnd_8152443 4186121767382152262970103 := by
  unfold tailWord_8152443
  simp only [CollatzResearch.WordTrace]
  refine ⟨297344024004098812260741983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198229349336065874840494655 297344024004098812260741983)
  ·
    refine ⟨446016036006148218391112975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297344024004098812260741983 446016036006148218391112975)
    ·
      refine ⟨669024054009222327586669463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446016036006148218391112975 669024054009222327586669463)
      ·
        refine ⟨1003536081013833491380004195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 669024054009222327586669463 1003536081013833491380004195)
        ·
          refine ⟨1505304121520750237070006293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1003536081013833491380004195 1505304121520750237070006293)
          ·
            refine ⟨70561130696285167362656545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1505304121520750237070006293 70561130696285167362656545)
            ·
              refine ⟨52920848022213875521992409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70561130696285167362656545 52920848022213875521992409)
              ·
                refine ⟨39690636016660406641494307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52920848022213875521992409 39690636016660406641494307)
                ·
                  refine ⟨59535954024990609962241461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39690636016660406641494307 59535954024990609962241461)
                  ·
                    refine ⟨5581495689842869683960137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59535954024990609962241461 5581495689842869683960137)
                    ·
                      refine ⟨4186121767382152262970103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5581495689842869683960137 4186121767382152262970103)
                      ·
                        rfl

theorem cell23_8152443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 5, 2].length) (baseStart_8152443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8152443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8152443 prefixEnd_8152443 := by exact prefixLift 8152443
  have htrace : WordTrace (prefixWord ++ tailWord_8152443) baseStart_8152443 baseEnd_8152443 := by
    simpa [prefixWord, tailWord_8152443, baseEnd_8152443] using wordTrace_append hprefix tailTrace_8152443
  have hstable : (prefixWord ++ tailWord_8152443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8152443).length < 2 ^ (prefixWord ++ tailWord_8152443).sum := by decide
  have hdescent : baseEnd_8152443 < baseStart_8152443 := by decide
  rcases family_descends (prefixWord ++ tailWord_8152443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8152483 : List Nat := [1, 1, 1, 4, 1, 3, 3, 1, 4, 4]
def baseStart_8152483 : Nat := 118140960795 + 8152483 * 2 ^ 59
def prefixEnd_8152483 : Nat := 4983230072969 + 3 ^ 40 * 8152483 * 2
def baseEnd_8152483 : Nat := 1395380768869444035489973

theorem tailTrace_8152483 : CollatzResearch.WordTrace tailWord_8152483 prefixEnd_8152483 1395380768869444035489973 := by
  unfold tailWord_8152483
  simp only [CollatzResearch.WordTrace]
  refine ⟨297345482923953899092198103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198230321949302599394798735 297345482923953899092198103)
  ·
    refine ⟨446018224385930848638297155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297345482923953899092198103 446018224385930848638297155)
    ·
      refine ⟨669027336578896272957445733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446018224385930848638297155 669027336578896272957445733)
      ·
        refine ⟨125442625608543051179521075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 669027336578896272957445733 125442625608543051179521075)
        ·
          refine ⟨188163938412814576769281613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125442625608543051179521075 188163938412814576769281613)
          ·
            refine ⟨70561476904805466288480605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188163938412814576769281613 70561476904805466288480605)
            ·
              refine ⟨26460553839302049858180227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70561476904805466288480605 26460553839302049858180227)
              ·
                refine ⟨39690830758953074787270341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26460553839302049858180227 39690830758953074787270341)
                ·
                  refine ⟨7442030767303701522613189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39690830758953074787270341 7442030767303701522613189)
                  ·
                    refine ⟨1395380768869444035489973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7442030767303701522613189 1395380768869444035489973)
                    ·
                      rfl

theorem cell23_8152483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 4, 4].length) (baseStart_8152483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8152483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8152483 prefixEnd_8152483 := by exact prefixLift 8152483
  have htrace : WordTrace (prefixWord ++ tailWord_8152483) baseStart_8152483 baseEnd_8152483 := by
    simpa [prefixWord, tailWord_8152483, baseEnd_8152483] using wordTrace_append hprefix tailTrace_8152483
  have hstable : (prefixWord ++ tailWord_8152483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8152483).length < 2 ^ (prefixWord ++ tailWord_8152483).sum := by decide
  have hdescent : baseEnd_8152483 < baseStart_8152483 := by decide
  rcases family_descends (prefixWord ++ tailWord_8152483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8152523 : List Nat := [1, 1, 1, 1, 3, 3, 2, 4, 1, 3, 3]
def baseStart_8152523 : Nat := 118140960795 + 8152523 * 2 ^ 59
def prefixEnd_8152523 : Nat := 4983230072969 + 3 ^ 40 * 8152523 * 2
def baseEnd_8152523 : Nat := 4186162845834511949969735

theorem tailTrace_8152523 : CollatzResearch.WordTrace tailWord_8152523 prefixEnd_8152523 4186162845834511949969735 := by
  unfold tailWord_8152523
  simp only [CollatzResearch.WordTrace]
  refine ⟨297346941843808985923654223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198231294562539323949102815 297346941843808985923654223)
  ·
    refine ⟨446020412765713478885481335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297346941843808985923654223 446020412765713478885481335)
    ·
      refine ⟨669030619148570218328222003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446020412765713478885481335 669030619148570218328222003)
      ·
        refine ⟨1003545928722855327492333005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 669030619148570218328222003 1003545928722855327492333005)
        ·
          refine ⟨376329723271070747809624877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1003545928722855327492333005 376329723271070747809624877)
          ·
            refine ⟨141123646226651530428609329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 376329723271070747809624877 141123646226651530428609329)
            ·
              refine ⟨105842734669988647821456997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141123646226651530428609329 105842734669988647821456997)
              ·
                refine ⟨19845512750622871466523187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105842734669988647821456997 19845512750622871466523187)
                ·
                  refine ⟨29768269125934307199784781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19845512750622871466523187 29768269125934307199784781)
                  ·
                    refine ⟨11163100922225365199919293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29768269125934307199784781 11163100922225365199919293)
                    ·
                      refine ⟨4186162845834511949969735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11163100922225365199919293 4186162845834511949969735)
                      ·
                        rfl

theorem cell23_8152523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 3, 3].length) (baseStart_8152523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8152523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8152523 prefixEnd_8152523 := by exact prefixLift 8152523
  have htrace : WordTrace (prefixWord ++ tailWord_8152523) baseStart_8152523 baseEnd_8152523 := by
    simpa [prefixWord, tailWord_8152523, baseEnd_8152523] using wordTrace_append hprefix tailTrace_8152523
  have hstable : (prefixWord ++ tailWord_8152523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8152523).length < 2 ^ (prefixWord ++ tailWord_8152523).sum := by decide
  have hdescent : baseEnd_8152523 < baseStart_8152523 := by decide
  rcases family_descends (prefixWord ++ tailWord_8152523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8152574 : List Nat := [4, 2, 2, 3, 1, 1, 1, 2, 1, 3, 3]
def baseStart_8152574 : Nat := 118140960795 + 8152574 * 2 ^ 59
def prefixEnd_8152574 : Nat := 4983230072969 + 3 ^ 40 * 8152574 * 2
def baseEnd_8152574 : Nat := 4186189033347891250432001

theorem tailTrace_8152574 : CollatzResearch.WordTrace tailWord_8152574 prefixEnd_8152574 4186189033347891250432001 := by
  unfold tailWord_8152574
  simp only [CollatzResearch.WordTrace]
  refine ⟨37168600245828027704220097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198232534644416147755840517 37168600245828027704220097)
  ·
    refine ⟨27876450184371020778165073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37168600245828027704220097 27876450184371020778165073)
    ·
      refine ⟨20907337638278265583623805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27876450184371020778165073 20907337638278265583623805)
      ·
        refine ⟨7840251614354349593858927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20907337638278265583623805 7840251614354349593858927)
        ·
          refine ⟨11760377421531524390788391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7840251614354349593858927 11760377421531524390788391)
          ·
            refine ⟨17640566132297286586182587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11760377421531524390788391 17640566132297286586182587)
            ·
              refine ⟨26460849198445929879273881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17640566132297286586182587 26460849198445929879273881)
              ·
                refine ⟨19845636898834447409455411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26460849198445929879273881 19845636898834447409455411)
                ·
                  refine ⟨29768455348251671114183117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19845636898834447409455411 29768455348251671114183117)
                  ·
                    refine ⟨11163170755594376667818669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29768455348251671114183117 11163170755594376667818669)
                    ·
                      refine ⟨4186189033347891250432001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11163170755594376667818669 4186189033347891250432001)
                      ·
                        rfl

theorem cell23_8152574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_8152574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8152574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8152574 prefixEnd_8152574 := by exact prefixLift 8152574
  have htrace : WordTrace (prefixWord ++ tailWord_8152574) baseStart_8152574 baseEnd_8152574 := by
    simpa [prefixWord, tailWord_8152574, baseEnd_8152574] using wordTrace_append hprefix tailTrace_8152574
  have hstable : (prefixWord ++ tailWord_8152574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8152574).length < 2 ^ (prefixWord ++ tailWord_8152574).sum := by decide
  have hdescent : baseEnd_8152574 < baseStart_8152574 := by decide
  rcases family_descends (prefixWord ++ tailWord_8152574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8152593 : List Nat := [1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 4]
def baseStart_8152593 : Nat := 118140960795 + 8152593 * 2 ^ 59
def prefixEnd_8152593 : Nat := 4983230072969 + 3 ^ 40 * 8152593 * 2
def baseEnd_8152593 : Nat := 4186198789480326676094413

theorem tailTrace_8152593 : CollatzResearch.WordTrace tailWord_8152593 prefixEnd_8152593 4186198789480326676094413 := by
  unfold tailWord_8152593
  simp only [CollatzResearch.WordTrace]
  refine ⟨297349494953555387878702433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198232996635703591919134955 297349494953555387878702433)
  ·
    refine ⟨223012121215166540909026825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297349494953555387878702433 223012121215166540909026825)
    ·
      refine ⟨167259090911374905681770119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223012121215166540909026825 167259090911374905681770119)
      ·
        refine ⟨250888636367062358522655179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167259090911374905681770119 250888636367062358522655179)
        ·
          refine ⟨376332954550593537783982769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250888636367062358522655179 376332954550593537783982769)
          ·
            refine ⟨282249715912945153337987077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 376332954550593537783982769 282249715912945153337987077)
            ·
              refine ⟨52921821733677216250872577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 282249715912945153337987077 52921821733677216250872577)
              ·
                refine ⟨39691366300257912188154433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52921821733677216250872577 39691366300257912188154433)
                ·
                  refine ⟨29768524725193434141115825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39691366300257912188154433 29768524725193434141115825)
                  ·
                    refine ⟨22326393543895075605836869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29768524725193434141115825 22326393543895075605836869)
                    ·
                      refine ⟨4186198789480326676094413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22326393543895075605836869 4186198789480326676094413)
                      ·
                        rfl

theorem cell23_8152593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 4].length) (baseStart_8152593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8152593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8152593 prefixEnd_8152593 := by exact prefixLift 8152593
  have htrace : WordTrace (prefixWord ++ tailWord_8152593) baseStart_8152593 baseEnd_8152593 := by
    simpa [prefixWord, tailWord_8152593, baseEnd_8152593] using wordTrace_append hprefix tailTrace_8152593
  have hstable : (prefixWord ++ tailWord_8152593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8152593).length < 2 ^ (prefixWord ++ tailWord_8152593).sum := by decide
  have hdescent : baseEnd_8152593 < baseStart_8152593 := by decide
  rcases family_descends (prefixWord ++ tailWord_8152593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8152713 : List Nat := [1, 2, 1, 1, 4, 1, 2, 1, 1, 1, 8]
def baseStart_8152713 : Nat := 118140960795 + 8152713 * 2 ^ 59
def prefixEnd_8152713 : Nat := 4983230072969 + 3 ^ 40 * 8152713 * 2
def baseEnd_8152713 : Nat := 4186260407158866206593861

theorem tailTrace_8152713 : CollatzResearch.WordTrace tailWord_8152713 prefixEnd_8152713 4186260407158866206593861 := by
  unfold tailWord_8152713
  simp only [CollatzResearch.WordTrace]
  refine ⟨297353871713120648373070793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198235914475413765582047195 297353871713120648373070793)
  ·
    refine ⟨223015403784840486279803095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297353871713120648373070793 223015403784840486279803095)
    ·
      refine ⟨334523105677260729419704643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223015403784840486279803095 334523105677260729419704643)
      ·
        refine ⟨501784658515891094129556965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334523105677260729419704643 501784658515891094129556965)
        ·
          refine ⟨94084623471729580149291931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 501784658515891094129556965 94084623471729580149291931)
          ·
            refine ⟨141126935207594370223937897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94084623471729580149291931 141126935207594370223937897)
            ·
              refine ⟨105845201405695777667953423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141126935207594370223937897 105845201405695777667953423)
              ·
                refine ⟨158767802108543666501930135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105845201405695777667953423 158767802108543666501930135)
                ·
                  refine ⟨238151703162815499752895203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158767802108543666501930135 238151703162815499752895203)
                  ·
                    refine ⟨357227554744223249629342805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 238151703162815499752895203 357227554744223249629342805)
                    ·
                      refine ⟨4186260407158866206593861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 357227554744223249629342805 4186260407158866206593861)
                      ·
                        rfl

theorem cell23_8152713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 1, 8].length) (baseStart_8152713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8152713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8152713 prefixEnd_8152713 := by exact prefixLift 8152713
  have htrace : WordTrace (prefixWord ++ tailWord_8152713) baseStart_8152713 baseEnd_8152713 := by
    simpa [prefixWord, tailWord_8152713, baseEnd_8152713] using wordTrace_append hprefix tailTrace_8152713
  have hstable : (prefixWord ++ tailWord_8152713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8152713).length < 2 ^ (prefixWord ++ tailWord_8152713).sum := by decide
  have hdescent : baseEnd_8152713 < baseStart_8152713 := by decide
  rcases family_descends (prefixWord ++ tailWord_8152713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8152714 : List Nat := [3, 1, 2, 3, 2, 3, 1, 1, 3, 4]
def baseStart_8152714 : Nat := 118140960795 + 8152714 * 2 ^ 59
def prefixEnd_8152714 : Nat := 4983230072969 + 3 ^ 40 * 8152714 * 2
def baseEnd_8152714 : Nat := 1395420306879840234227119

theorem tailTrace_8152714 : CollatzResearch.WordTrace tailWord_8152714 prefixEnd_8152714 1395420306879840234227119 := by
  unfold tailWord_8152714
  simp only [CollatzResearch.WordTrace]
  refine ⟨74338477046529256385964299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198235938790744683695904797 74338477046529256385964299)
  ·
    refine ⟨111507715569793884578946449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74338477046529256385964299 111507715569793884578946449)
    ·
      refine ⟨83630786677345413434209837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111507715569793884578946449 83630786677345413434209837)
      ·
        refine ⟨31361545004004530037828689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83630786677345413434209837 31361545004004530037828689)
        ·
          refine ⟨23521158753003397528371517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31361545004004530037828689 23521158753003397528371517)
          ·
            refine ⟨8820434532376274073139319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23521158753003397528371517 8820434532376274073139319)
            ·
              refine ⟨13230651798564411109708979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8820434532376274073139319 13230651798564411109708979)
              ·
                refine ⟨19845977697846616664563469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13230651798564411109708979 19845977697846616664563469)
                ·
                  refine ⟨7442241636692481249211301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19845977697846616664563469 7442241636692481249211301)
                  ·
                    refine ⟨1395420306879840234227119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7442241636692481249211301 1395420306879840234227119)
                    ·
                      rfl

theorem cell23_8152714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 3, 4].length) (baseStart_8152714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8152714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8152714 prefixEnd_8152714 := by exact prefixLift 8152714
  have htrace : WordTrace (prefixWord ++ tailWord_8152714) baseStart_8152714 baseEnd_8152714 := by
    simpa [prefixWord, tailWord_8152714, baseEnd_8152714] using wordTrace_append hprefix tailTrace_8152714
  have hstable : (prefixWord ++ tailWord_8152714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8152714).length < 2 ^ (prefixWord ++ tailWord_8152714).sum := by decide
  have hdescent : baseEnd_8152714 < baseStart_8152714 := by decide
  rcases family_descends (prefixWord ++ tailWord_8152714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8152727 : List Nat := [1, 1, 3, 3, 2, 2, 4, 1, 6]
def baseStart_8152727 : Nat := 118140960795 + 8152727 * 2 ^ 59
def prefixEnd_8152727 : Nat := 4983230072969 + 3 ^ 40 * 8152727 * 2
def baseEnd_8152727 : Nat := 465140843987558794646533

theorem tailTrace_8152727 : CollatzResearch.WordTrace tailWord_8152727 prefixEnd_8152727 465140843987558794646533 := by
  unfold tailWord_8152727
  simp only [CollatzResearch.WordTrace]
  refine ⟨297354382335069928764080435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198236254890046619176053623 297354382335069928764080435)
  ·
    refine ⟨446031573502604893146120653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297354382335069928764080435 446031573502604893146120653)
    ·
      refine ⟨167261840063476834929795245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 446031573502604893146120653 167261840063476834929795245)
      ·
        refine ⟨62723190023803813098673217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167261840063476834929795245 62723190023803813098673217)
        ·
          refine ⟨47042392517852859824004913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62723190023803813098673217 47042392517852859824004913)
          ·
            refine ⟨35281794388389644868003685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47042392517852859824004913 35281794388389644868003685)
            ·
              refine ⟨6615336447823058412750691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35281794388389644868003685 6615336447823058412750691)
              ·
                refine ⟨9923004671734587619126037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6615336447823058412750691 9923004671734587619126037)
                ·
                  refine ⟨465140843987558794646533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9923004671734587619126037 465140843987558794646533)
                  ·
                    rfl

theorem cell23_8152727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 1, 6].length) (baseStart_8152727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8152727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8152727 prefixEnd_8152727 := by exact prefixLift 8152727
  have htrace : WordTrace (prefixWord ++ tailWord_8152727) baseStart_8152727 baseEnd_8152727 := by
    simpa [prefixWord, tailWord_8152727, baseEnd_8152727] using wordTrace_append hprefix tailTrace_8152727
  have hstable : (prefixWord ++ tailWord_8152727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8152727).length < 2 ^ (prefixWord ++ tailWord_8152727).sum := by decide
  have hdescent : baseEnd_8152727 < baseStart_8152727 := by decide
  rcases family_descends (prefixWord ++ tailWord_8152727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8152764 : List Nat := [2, 2, 2, 3, 1, 2, 2, 2, 2, 3, 2]
def baseStart_8152764 : Nat := 118140960795 + 8152764 * 2 ^ 59
def prefixEnd_8152764 : Nat := 4983230072969 + 3 ^ 40 * 8152764 * 2
def baseEnd_8152764 : Nat := 4186286594672245507056127

theorem tailTrace_8152764 : CollatzResearch.WordTrace tailWord_8152764 prefixEnd_8152764 4186286594672245507056127 := by
  unfold tailWord_8152764
  simp only [CollatzResearch.WordTrace]
  refine ⟨148677865917967942041588673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198237154557290589388784897 148677865917967942041588673)
  ·
    refine ⟨111508399438475956531191505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148677865917967942041588673 111508399438475956531191505)
    ·
      refine ⟨83631299578856967398393629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111508399438475956531191505 83631299578856967398393629)
      ·
        refine ⟨31361737342071362774397611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83631299578856967398393629 31361737342071362774397611)
        ·
          refine ⟨47042606013107044161596417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31361737342071362774397611 47042606013107044161596417)
          ·
            refine ⟨35281954509830283121197313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47042606013107044161596417 35281954509830283121197313)
            ·
              refine ⟨26461465882372712340897985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35281954509830283121197313 26461465882372712340897985)
              ·
                refine ⟨19846099411779534255673489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26461465882372712340897985 19846099411779534255673489)
                ·
                  refine ⟨14884574558834650691755117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19846099411779534255673489 14884574558834650691755117)
                  ·
                    refine ⟨5581715459562994009408169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14884574558834650691755117 5581715459562994009408169)
                    ·
                      refine ⟨4186286594672245507056127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5581715459562994009408169 4186286594672245507056127)
                      ·
                        rfl

theorem cell23_8152764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_8152764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8152764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8152764 prefixEnd_8152764 := by exact prefixLift 8152764
  have htrace : WordTrace (prefixWord ++ tailWord_8152764) baseStart_8152764 baseEnd_8152764 := by
    simpa [prefixWord, tailWord_8152764, baseEnd_8152764] using wordTrace_append hprefix tailTrace_8152764
  have hstable : (prefixWord ++ tailWord_8152764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8152764).length < 2 ^ (prefixWord ++ tailWord_8152764).sum := by decide
  have hdescent : baseEnd_8152764 < baseStart_8152764 := by decide
  rcases family_descends (prefixWord ++ tailWord_8152764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8152794 : List Nat := [3, 1, 1, 2, 2, 3, 1, 1, 5, 2, 2]
def baseStart_8152794 : Nat := 118140960795 + 8152794 * 2 ^ 59
def prefixEnd_8152794 : Nat := 4983230072969 + 3 ^ 40 * 8152794 * 2
def baseEnd_8152794 : Nat := 4186301999091880389680989

theorem tailTrace_8152794 : CollatzResearch.WordTrace tailWord_8152794 prefixEnd_8152794 4186301999091880389680989 := by
  unfold tailWord_8152794
  simp only [CollatzResearch.WordTrace]
  refine ⟨74339206506456799801692359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198237884017218132804512957 74339206506456799801692359)
  ·
    refine ⟨111508809759685199702538539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74339206506456799801692359 111508809759685199702538539)
    ·
      refine ⟨167263214639527799553807809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111508809759685199702538539 167263214639527799553807809)
      ·
        refine ⟨125447410979645849665355857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167263214639527799553807809 125447410979645849665355857)
        ·
          refine ⟨94085558234734387249016893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125447410979645849665355857 94085558234734387249016893)
          ·
            refine ⟨35282084338025395218381335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94085558234734387249016893 35282084338025395218381335)
            ·
              refine ⟨52923126507038092827572003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35282084338025395218381335 52923126507038092827572003)
              ·
                refine ⟨79384689760557139241358005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52923126507038092827572003 79384689760557139241358005)
                ·
                  refine ⟨7442314665052231803877313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79384689760557139241358005 7442314665052231803877313)
                  ·
                    refine ⟨5581735998789173852907985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7442314665052231803877313 5581735998789173852907985)
                    ·
                      refine ⟨4186301999091880389680989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5581735998789173852907985 4186301999091880389680989)
                      ·
                        rfl

theorem cell23_8152794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 5, 2, 2].length) (baseStart_8152794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8152794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8152794 prefixEnd_8152794 := by exact prefixLift 8152794
  have htrace : WordTrace (prefixWord ++ tailWord_8152794) baseStart_8152794 baseEnd_8152794 := by
    simpa [prefixWord, tailWord_8152794, baseEnd_8152794] using wordTrace_append hprefix tailTrace_8152794
  have hstable : (prefixWord ++ tailWord_8152794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8152794).length < 2 ^ (prefixWord ++ tailWord_8152794).sum := by decide
  have hdescent : baseEnd_8152794 < baseStart_8152794 := by decide
  rcases family_descends (prefixWord ++ tailWord_8152794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8152811 : List Nat := [1, 1, 1, 1, 2, 4, 3, 5, 1, 2, 2]
def baseStart_8152811 : Nat := 118140960795 + 8152811 * 2 ^ 59
def prefixEnd_8152811 : Nat := 4983230072969 + 3 ^ 40 * 8152811 * 2
def baseEnd_8152811 : Nat := 4186310728263006823168411

theorem tailTrace_8152811 : CollatzResearch.WordTrace tailWord_8152811 prefixEnd_8152811 4186310728263006823168411 := by
  unfold tailWord_8152811
  simp only [CollatzResearch.WordTrace]
  refine ⟨297357446066765611110138287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198238297377843740740092191 297357446066765611110138287)
  ·
    refine ⟨446036169100148416665207431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297357446066765611110138287 446036169100148416665207431)
    ·
      refine ⟨669054253650222624997811147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446036169100148416665207431 669054253650222624997811147)
      ·
        refine ⟨1003581380475333937496716721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 669054253650222624997811147 1003581380475333937496716721)
        ·
          refine ⟨752686035356500453122537541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1003581380475333937496716721 752686035356500453122537541)
          ·
            refine ⟨141128631629343834960475789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 752686035356500453122537541 141128631629343834960475789)
            ·
              refine ⟨52923236861003938110178421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141128631629343834960475789 52923236861003938110178421)
              ·
                refine ⟨4961553455719119197829227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52923236861003938110178421 4961553455719119197829227)
                ·
                  refine ⟨7442330183578678796743841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4961553455719119197829227 7442330183578678796743841)
                  ·
                    refine ⟨5581747637684009097557881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7442330183578678796743841 5581747637684009097557881)
                    ·
                      refine ⟨4186310728263006823168411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5581747637684009097557881 4186310728263006823168411)
                      ·
                        rfl

theorem cell23_8152811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 5, 1, 2, 2].length) (baseStart_8152811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8152811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8152811 prefixEnd_8152811 := by exact prefixLift 8152811
  have htrace : WordTrace (prefixWord ++ tailWord_8152811) baseStart_8152811 baseEnd_8152811 := by
    simpa [prefixWord, tailWord_8152811, baseEnd_8152811] using wordTrace_append hprefix tailTrace_8152811
  have hstable : (prefixWord ++ tailWord_8152811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8152811).length < 2 ^ (prefixWord ++ tailWord_8152811).sum := by decide
  have hdescent : baseEnd_8152811 < baseStart_8152811 := by decide
  rcases family_descends (prefixWord ++ tailWord_8152811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8152814 : List Nat := [4, 1, 2, 1, 1, 2, 3, 3, 1, 2, 3]
def baseStart_8152814 : Nat := 118140960795 + 8152814 * 2 ^ 59
def prefixEnd_8152814 : Nat := 4983230072969 + 3 ^ 40 * 8152814 * 2
def baseEnd_8152814 : Nat := 4186312268704970311430897

theorem tailTrace_8152814 : CollatzResearch.WordTrace tailWord_8152814 prefixEnd_8152814 4186312268704970311430897 := by
  unfold tailWord_8152814
  simp only [CollatzResearch.WordTrace]
  refine ⟨37169694435719342827812187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198238370323836495081664997 37169694435719342827812187)
  ·
    refine ⟨55754541653579014241718281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37169694435719342827812187 55754541653579014241718281)
    ·
      refine ⟨41815906240184260681288711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55754541653579014241718281 41815906240184260681288711)
      ·
        refine ⟨62723859360276391021933067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41815906240184260681288711 62723859360276391021933067)
        ·
          refine ⟨94085789040414586532899601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62723859360276391021933067 94085789040414586532899601)
          ·
            refine ⟨70564341780310939899674701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94085789040414586532899601 70564341780310939899674701)
            ·
              refine ⟨26461628167616602462378013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70564341780310939899674701 26461628167616602462378013)
              ·
                refine ⟨9923110562856225923391755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26461628167616602462378013 9923110562856225923391755)
                ·
                  refine ⟨14884665844284338885087633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9923110562856225923391755 14884665844284338885087633)
                  ·
                    refine ⟨11163499383213254163815725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14884665844284338885087633 11163499383213254163815725)
                    ·
                      refine ⟨4186312268704970311430897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11163499383213254163815725 4186312268704970311430897)
                      ·
                        rfl

theorem cell23_8152814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_8152814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8152814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8152814 prefixEnd_8152814 := by exact prefixLift 8152814
  have htrace : WordTrace (prefixWord ++ tailWord_8152814) baseStart_8152814 baseEnd_8152814 := by
    simpa [prefixWord, tailWord_8152814, baseEnd_8152814] using wordTrace_append hprefix tailTrace_8152814
  have hstable : (prefixWord ++ tailWord_8152814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8152814).length < 2 ^ (prefixWord ++ tailWord_8152814).sum := by decide
  have hdescent : baseEnd_8152814 < baseStart_8152814 := by decide
  rcases family_descends (prefixWord ++ tailWord_8152814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8152844 : List Nat := [2, 2, 1, 2, 2, 1, 2, 5, 2, 1, 3]
def baseStart_8152844 : Nat := 118140960795 + 8152844 * 2 ^ 59
def prefixEnd_8152844 : Nat := 4983230072969 + 3 ^ 40 * 8152844 * 2
def baseEnd_8152844 : Nat := 4186327673124605194055759

theorem tailTrace_8152844 : CollatzResearch.WordTrace tailWord_8152844 prefixEnd_8152844 4186327673124605194055759 := by
  unfold tailWord_8152844
  simp only [CollatzResearch.WordTrace]
  refine ⟨148679324837823028873044793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198239099783764038497393057 148679324837823028873044793)
  ·
    refine ⟨111509493628367271654783595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148679324837823028873044793 111509493628367271654783595)
    ·
      refine ⟨167264240442550907482175393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111509493628367271654783595 167264240442550907482175393)
      ·
        refine ⟨125448180331913180611631545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167264240442550907482175393 125448180331913180611631545)
        ·
          refine ⟨94086135248934885458723659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125448180331913180611631545 94086135248934885458723659)
          ·
            refine ⟨141129202873402328188085489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94086135248934885458723659 141129202873402328188085489)
            ·
              refine ⟨105846902155051746141064117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141129202873402328188085489 105846902155051746141064117)
              ·
                refine ⟨9923147077036101200724761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105846902155051746141064117 9923147077036101200724761)
                ·
                  refine ⟨7442360307777075900543571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9923147077036101200724761 7442360307777075900543571)
                  ·
                    refine ⟨11163540461665613850815357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7442360307777075900543571 11163540461665613850815357)
                    ·
                      refine ⟨4186327673124605194055759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11163540461665613850815357 4186327673124605194055759)
                      ·
                        rfl

theorem cell23_8152844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 5, 2, 1, 3].length) (baseStart_8152844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8152844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8152844 prefixEnd_8152844 := by exact prefixLift 8152844
  have htrace : WordTrace (prefixWord ++ tailWord_8152844) baseStart_8152844 baseEnd_8152844 := by
    simpa [prefixWord, tailWord_8152844, baseEnd_8152844] using wordTrace_append hprefix tailTrace_8152844
  have hstable : (prefixWord ++ tailWord_8152844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8152844).length < 2 ^ (prefixWord ++ tailWord_8152844).sum := by decide
  have hdescent : baseEnd_8152844 < baseStart_8152844 := by decide
  rcases family_descends (prefixWord ++ tailWord_8152844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8152895 : List Nat := [1, 1, 2, 2, 7, 1, 2, 1, 2, 1, 3]
def baseStart_8152895 : Nat := 118140960795 + 8152895 * 2 ^ 59
def prefixEnd_8152895 : Nat := 4983230072969 + 3 ^ 40 * 8152895 * 2
def baseEnd_8152895 : Nat := 4186353860637984494518025

theorem tailTrace_8152895 : CollatzResearch.WordTrace tailWord_8152895 prefixEnd_8152895 4186353860637984494518025 := by
  unfold tailWord_8152895
  simp only [CollatzResearch.WordTrace]
  refine ⟨297360509798461293456196139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198240339865640862304130759 297360509798461293456196139)
  ·
    refine ⟨446040764697691940184294209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297360509798461293456196139 446040764697691940184294209)
    ·
      refine ⟨334530573523268955138220657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446040764697691940184294209 334530573523268955138220657)
      ·
        refine ⟨250897930142451716353665493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334530573523268955138220657 250897930142451716353665493)
        ·
          refine ⟨5880420237713712102039035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 250897930142451716353665493 5880420237713712102039035)
          ·
            refine ⟨8820630356570568153058553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5880420237713712102039035 8820630356570568153058553)
            ·
              refine ⟨6615472767427926114793915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8820630356570568153058553 6615472767427926114793915)
              ·
                refine ⟨9923209151141889172190873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6615472767427926114793915 9923209151141889172190873)
                ·
                  refine ⟨7442406863356416879143155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9923209151141889172190873 7442406863356416879143155)
                  ·
                    refine ⟨11163610295034625318714733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7442406863356416879143155 11163610295034625318714733)
                    ·
                      refine ⟨4186353860637984494518025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11163610295034625318714733 4186353860637984494518025)
                      ·
                        rfl

theorem cell23_8152895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 1, 2, 1, 3].length) (baseStart_8152895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8152895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8152895 prefixEnd_8152895 := by exact prefixLift 8152895
  have htrace : WordTrace (prefixWord ++ tailWord_8152895) baseStart_8152895 baseEnd_8152895 := by
    simpa [prefixWord, tailWord_8152895, baseEnd_8152895] using wordTrace_append hprefix tailTrace_8152895
  have hstable : (prefixWord ++ tailWord_8152895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8152895).length < 2 ^ (prefixWord ++ tailWord_8152895).sum := by decide
  have hdescent : baseEnd_8152895 < baseStart_8152895 := by decide
  rcases family_descends (prefixWord ++ tailWord_8152895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8152901 : List Nat := [1, 3, 1, 1, 1, 2, 5, 3, 2, 2, 2]
def baseStart_8152901 : Nat := 118140960795 + 8152901 * 2 ^ 59
def prefixEnd_8152901 : Nat := 4983230072969 + 3 ^ 40 * 8152901 * 2
def baseEnd_8152901 : Nat := 4186356941521911471042997

theorem tailTrace_8152901 : CollatzResearch.WordTrace tailWord_8152901 prefixEnd_8152901 4186356941521911471042997 := by
  unfold tailWord_8152901
  simp only [CollatzResearch.WordTrace]
  refine ⟨297360728636439556480914557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198240485757626370987276371 297360728636439556480914557)
  ·
    refine ⟨111510273238664833680342959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297360728636439556480914557 111510273238664833680342959)
    ·
      refine ⟨167265409857997250520514439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111510273238664833680342959 167265409857997250520514439)
      ·
        refine ⟨250898114786995875780771659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167265409857997250520514439 250898114786995875780771659)
        ·
          refine ⟨376347172180493813671157489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250898114786995875780771659 376347172180493813671157489)
          ·
            refine ⟨282260379135370360253368117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 376347172180493813671157489 282260379135370360253368117)
            ·
              refine ⟨26461910543940971273753261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 282260379135370360253368117 26461910543940971273753261)
              ·
                refine ⟨9923216453977864227657473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26461910543940971273753261 9923216453977864227657473)
                ·
                  refine ⟨7442412340483398170743105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9923216453977864227657473 7442412340483398170743105)
                  ·
                    refine ⟨5581809255362548628057329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7442412340483398170743105 5581809255362548628057329)
                    ·
                      refine ⟨4186356941521911471042997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5581809255362548628057329 4186356941521911471042997)
                      ·
                        rfl

theorem cell23_8152901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 3, 2, 2, 2].length) (baseStart_8152901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8152901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8152901 prefixEnd_8152901 := by exact prefixLift 8152901
  have htrace : WordTrace (prefixWord ++ tailWord_8152901) baseStart_8152901 baseEnd_8152901 := by
    simpa [prefixWord, tailWord_8152901, baseEnd_8152901] using wordTrace_append hprefix tailTrace_8152901
  have hstable : (prefixWord ++ tailWord_8152901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8152901).length < 2 ^ (prefixWord ++ tailWord_8152901).sum := by decide
  have hdescent : baseEnd_8152901 < baseStart_8152901 := by decide
  rcases family_descends (prefixWord ++ tailWord_8152901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8152941 : List Nat := [1, 5, 1, 1, 1, 1, 6, 2, 5]
def baseStart_8152941 : Nat := 118140960795 + 8152941 * 2 ^ 59
def prefixEnd_8152941 : Nat := 4983230072969 + 3 ^ 40 * 8152941 * 2
def baseEnd_8152941 : Nat := 465153053416454590504757

theorem tailTrace_8152941 : CollatzResearch.WordTrace tailWord_8152941 prefixEnd_8152941 465153053416454590504757 := by
  unfold tailWord_8152941
  simp only [CollatzResearch.WordTrace]
  refine ⟨297362187556294643312370677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198241458370863095541580451 297362187556294643312370677)
  ·
    refine ⟨27877705083402622810534751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 297362187556294643312370677 27877705083402622810534751)
    ·
      refine ⟨41816557625103934215802127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27877705083402622810534751 41816557625103934215802127)
      ·
        refine ⟨62724836437655901323703191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41816557625103934215802127 62724836437655901323703191)
        ·
          refine ⟨94087254656483851985554787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62724836437655901323703191 94087254656483851985554787)
          ·
            refine ⟨141130881984725777978332181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94087254656483851985554787 141130881984725777978332181)
            ·
              refine ⟨6615510093034020842734321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 141130881984725777978332181 6615510093034020842734321)
              ·
                refine ⟨4961632569775515632050741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6615510093034020842734321 4961632569775515632050741)
                ·
                  refine ⟨465153053416454590504757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4961632569775515632050741 465153053416454590504757)
                  ·
                    rfl

theorem cell23_8152941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 2, 5].length) (baseStart_8152941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8152941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8152941 prefixEnd_8152941 := by exact prefixLift 8152941
  have htrace : WordTrace (prefixWord ++ tailWord_8152941) baseStart_8152941 baseEnd_8152941 := by
    simpa [prefixWord, tailWord_8152941, baseEnd_8152941] using wordTrace_append hprefix tailTrace_8152941
  have hstable : (prefixWord ++ tailWord_8152941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8152941).length < 2 ^ (prefixWord ++ tailWord_8152941).sum := by decide
  have hdescent : baseEnd_8152941 < baseStart_8152941 := by decide
  rcases family_descends (prefixWord ++ tailWord_8152941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8152957 : List Nat := [1, 4, 1, 1, 2, 1, 1, 4, 1, 3, 4]
def baseStart_8152957 : Nat := 118140960795 + 8152957 * 2 ^ 59
def prefixEnd_8152957 : Nat := 4983230072969 + 3 ^ 40 * 8152957 * 2
def baseEnd_8152957 : Nat := 4186385696438563251942739

theorem tailTrace_8152957 : CollatzResearch.WordTrace tailWord_8152957 prefixEnd_8152957 4186385696438563251942739 := by
  unfold tailWord_8152957
  simp only [CollatzResearch.WordTrace]
  refine ⟨297362771124236678044953125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198241847416157785363302083 297362771124236678044953125)
  ·
    refine ⟨55755519585794377133428711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 297362771124236678044953125 55755519585794377133428711)
    ·
      refine ⟨83633279378691565700143067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55755519585794377133428711 83633279378691565700143067)
      ·
        refine ⟨125449919068037348550214601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83633279378691565700143067 125449919068037348550214601)
        ·
          refine ⟨94087439301028011412660951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125449919068037348550214601 94087439301028011412660951)
          ·
            refine ⟨141131158951542017118991427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94087439301028011412660951 141131158951542017118991427)
            ·
              refine ⟨211696738427313025678487141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141131158951542017118991427 211696738427313025678487141)
              ·
                refine ⟨39693138455121192314716339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 211696738427313025678487141 39693138455121192314716339)
                ·
                  refine ⟨59539707682681788472074509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39693138455121192314716339 59539707682681788472074509)
                  ·
                    refine ⟨22327390381005670677027941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59539707682681788472074509 22327390381005670677027941)
                    ·
                      refine ⟨4186385696438563251942739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22327390381005670677027941 4186385696438563251942739)
                      ·
                        rfl

theorem cell23_8152957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_8152957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8152957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8152957 prefixEnd_8152957 := by exact prefixLift 8152957
  have htrace : WordTrace (prefixWord ++ tailWord_8152957) baseStart_8152957 baseEnd_8152957 := by
    simpa [prefixWord, tailWord_8152957, baseEnd_8152957] using wordTrace_append hprefix tailTrace_8152957
  have hstable : (prefixWord ++ tailWord_8152957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8152957).length < 2 ^ (prefixWord ++ tailWord_8152957).sum := by decide
  have hdescent : baseEnd_8152957 < baseStart_8152957 := by decide
  rcases family_descends (prefixWord ++ tailWord_8152957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8153017 : List Nat := [1, 2, 1, 4, 2, 1, 1, 2, 1, 2, 6]
def baseStart_8153017 : Nat := 118140960795 + 8153017 * 2 ^ 59
def prefixEnd_8153017 : Nat := 4983230072969 + 3 ^ 40 * 8153017 * 2
def baseEnd_8153017 : Nat := 4186416505277833017192463

theorem tailTrace_8153017 : CollatzResearch.WordTrace tailWord_8153017 prefixEnd_8153017 4186416505277833017192463 := by
  unfold tailWord_8153017
  simp only [CollatzResearch.WordTrace]
  refine ⟨297364959504019308292137305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198243306336012872194758203 297364959504019308292137305)
  ·
    refine ⟨223023719628014481219102979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297364959504019308292137305 223023719628014481219102979)
    ·
      refine ⟨334535579442021721828654469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223023719628014481219102979 334535579442021721828654469)
      ·
        refine ⟨62725421145379072842872713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 334535579442021721828654469 62725421145379072842872713)
        ·
          refine ⟨47044065859034304632154535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62725421145379072842872713 47044065859034304632154535)
          ·
            refine ⟨70566098788551456948231803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47044065859034304632154535 70566098788551456948231803)
            ·
              refine ⟨105849148182827185422347705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70566098788551456948231803 105849148182827185422347705)
              ·
                refine ⟨79386861137120389066760779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105849148182827185422347705 79386861137120389066760779)
                ·
                  refine ⟨119080291705680583600141169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79386861137120389066760779 119080291705680583600141169)
                  ·
                    refine ⟨89310218779260437700105877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 119080291705680583600141169 89310218779260437700105877)
                    ·
                      refine ⟨4186416505277833017192463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89310218779260437700105877 4186416505277833017192463)
                      ·
                        rfl

theorem cell23_8153017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_8153017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8153017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8153017 prefixEnd_8153017 := by exact prefixLift 8153017
  have htrace : WordTrace (prefixWord ++ tailWord_8153017) baseStart_8153017 baseEnd_8153017 := by
    simpa [prefixWord, tailWord_8153017, baseEnd_8153017] using wordTrace_append hprefix tailTrace_8153017
  have hstable : (prefixWord ++ tailWord_8153017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8153017).length < 2 ^ (prefixWord ++ tailWord_8153017).sum := by decide
  have hdescent : baseEnd_8153017 < baseStart_8153017 := by decide
  rcases family_descends (prefixWord ++ tailWord_8153017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8153052 : List Nat := [2, 2, 6, 1, 1, 2, 1, 1, 3, 4]
def baseStart_8153052 : Nat := 118140960795 + 8153052 * 2 ^ 59
def prefixEnd_8153052 : Nat := 4983230072969 + 3 ^ 40 * 8153052 * 2
def baseEnd_8153052 : Nat := 1395478159033580126751601

theorem tailTrace_8153052 : CollatzResearch.WordTrace tailWord_8153052 prefixEnd_8153052 1395478159033580126751601 := by
  unfold tailWord_8153052
  simp only [CollatzResearch.WordTrace]
  refine ⟨148683118029446254634830705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198244157372595006179774273 148683118029446254634830705)
  ·
    refine ⟨111512338522084690976123029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148683118029446254634830705 111512338522084690976123029)
    ·
      refine ⟨5227140868222719889505767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 111512338522084690976123029 5227140868222719889505767)
      ·
        refine ⟨7840711302334079834258651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5227140868222719889505767 7840711302334079834258651)
        ·
          refine ⟨11761066953501119751387977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7840711302334079834258651 11761066953501119751387977)
          ·
            refine ⟨8820800215125839813540983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11761066953501119751387977 8820800215125839813540983)
            ·
              refine ⟨13231200322688759720311475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8820800215125839813540983 13231200322688759720311475)
              ·
                refine ⟨19846800484033139580467213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13231200322688759720311475 19846800484033139580467213)
                ·
                  refine ⟨7442550181512427342675205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19846800484033139580467213 7442550181512427342675205)
                  ·
                    refine ⟨1395478159033580126751601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7442550181512427342675205 1395478159033580126751601)
                    ·
                      rfl

theorem cell23_8153052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_8153052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8153052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8153052 prefixEnd_8153052 := by exact prefixLift 8153052
  have htrace : WordTrace (prefixWord ++ tailWord_8153052) baseStart_8153052 baseEnd_8153052 := by
    simpa [prefixWord, tailWord_8153052, baseEnd_8153052] using wordTrace_append hprefix tailTrace_8153052
  have hstable : (prefixWord ++ tailWord_8153052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8153052).length < 2 ^ (prefixWord ++ tailWord_8153052).sum := by decide
  have hdescent : baseEnd_8153052 < baseStart_8153052 := by decide
  rcases family_descends (prefixWord ++ tailWord_8153052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8153064 : List Nat := [2, 1, 4, 1, 1, 1, 1, 4, 3, 1, 4]
def baseStart_8153064 : Nat := 118140960795 + 8153064 * 2 ^ 59
def prefixEnd_8153064 : Nat := 4983230072969 + 3 ^ 40 * 8153064 * 2
def baseEnd_8153064 : Nat := 4186440638868594333304747

theorem tailTrace_8153064 : CollatzResearch.WordTrace tailWord_8153064 prefixEnd_8153064 4186440638868594333304747 := by
  unfold tailWord_8153064
  simp only [CollatzResearch.WordTrace]
  refine ⟨148683336867424517659549123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198244449156566023546065497 148683336867424517659549123)
  ·
    refine ⟨223025005301136776489323685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148683336867424517659549123 223025005301136776489323685)
    ·
      refine ⟨41817188493963145591748191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223025005301136776489323685 41817188493963145591748191)
      ·
        refine ⟨62725782740944718387622287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41817188493963145591748191 62725782740944718387622287)
        ·
          refine ⟨94088674111417077581433431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62725782740944718387622287 94088674111417077581433431)
          ·
            refine ⟨141133011167125616372150147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94088674111417077581433431 141133011167125616372150147)
            ·
              refine ⟨211699516750688424558225221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141133011167125616372150147 211699516750688424558225221)
              ·
                refine ⟨39693659390754079604667229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 211699516750688424558225221 39693659390754079604667229)
                ·
                  refine ⟨14885122271532779851750211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39693659390754079604667229 14885122271532779851750211)
                  ·
                    refine ⟨22327683407299169777625317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14885122271532779851750211 22327683407299169777625317)
                    ·
                      refine ⟨4186440638868594333304747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22327683407299169777625317 4186440638868594333304747)
                      ·
                        rfl

theorem cell23_8153064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_8153064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8153064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8153064 prefixEnd_8153064 := by exact prefixLift 8153064
  have htrace : WordTrace (prefixWord ++ tailWord_8153064) baseStart_8153064 baseEnd_8153064 := by
    simpa [prefixWord, tailWord_8153064, baseEnd_8153064] using wordTrace_append hprefix tailTrace_8153064
  have hstable : (prefixWord ++ tailWord_8153064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8153064).length < 2 ^ (prefixWord ++ tailWord_8153064).sum := by decide
  have hdescent : baseEnd_8153064 < baseStart_8153064 := by decide
  rcases family_descends (prefixWord ++ tailWord_8153064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8153081 : List Nat := [1, 2, 1, 3, 1, 4, 3, 2, 1, 1, 4]
def baseStart_8153081 : Nat := 118140960795 + 8153081 * 2 ^ 59
def prefixEnd_8153081 : Nat := 4983230072969 + 3 ^ 40 * 8153081 * 2
def baseEnd_8153081 : Nat := 4186449368039720766792169

theorem tailTrace_8153081 : CollatzResearch.WordTrace tailWord_8153081 prefixEnd_8153081 4186449368039720766792169 := by
  unfold tailWord_8153081
  simp only [CollatzResearch.WordTrace]
  refine ⟨297367293775787447222467097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198244862517191631481644731 297367293775787447222467097)
  ·
    refine ⟨223025470331840585416850323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297367293775787447222467097 223025470331840585416850323)
    ·
      refine ⟨334538205497760878125275485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223025470331840585416850323 334538205497760878125275485)
      ·
        refine ⟨125451827061660329296978307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334538205497760878125275485 125451827061660329296978307)
        ·
          refine ⟨188177740592490493945467461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125451827061660329296978307 188177740592490493945467461)
          ·
            refine ⟨35283326361091967614775149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188177740592490493945467461 35283326361091967614775149)
            ·
              refine ⟨13231247385409487855540681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35283326361091967614775149 13231247385409487855540681)
              ·
                refine ⟨9923435539057115891655511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13231247385409487855540681 9923435539057115891655511)
                ·
                  refine ⟨14885153308585673837483267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9923435539057115891655511 14885153308585673837483267)
                  ·
                    refine ⟨22327729962878510756224901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14885153308585673837483267 22327729962878510756224901)
                    ·
                      refine ⟨4186449368039720766792169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22327729962878510756224901 4186449368039720766792169)
                      ·
                        rfl

theorem cell23_8153081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 2, 1, 1, 4].length) (baseStart_8153081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8153081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8153081 prefixEnd_8153081 := by exact prefixLift 8153081
  have htrace : WordTrace (prefixWord ++ tailWord_8153081) baseStart_8153081 baseEnd_8153081 := by
    simpa [prefixWord, tailWord_8153081, baseEnd_8153081] using wordTrace_append hprefix tailTrace_8153081
  have hstable : (prefixWord ++ tailWord_8153081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8153081).length < 2 ^ (prefixWord ++ tailWord_8153081).sum := by decide
  have hdescent : baseEnd_8153081 < baseStart_8153081 := by decide
  rcases family_descends (prefixWord ++ tailWord_8153081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8153109 : List Nat := [1, 3, 2, 1, 6, 1, 2, 2, 1, 1, 3]
def baseStart_8153109 : Nat := 118140960795 + 8153109 * 2 ^ 59
def prefixEnd_8153109 : Nat := 4983230072969 + 3 ^ 40 * 8153109 * 2
def baseEnd_8153109 : Nat := 4186463745498046657242041

theorem tailTrace_8153109 : CollatzResearch.WordTrace tailWord_8153109 prefixEnd_8153109 4186463745498046657242041 := by
  unfold tailWord_8153109
  simp only [CollatzResearch.WordTrace]
  refine ⟨297368315019686008004486381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198245543346457338669657587 297368315019686008004486381)
  ·
    refine ⟨111513118132382253001682393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297368315019686008004486381 111513118132382253001682393)
    ·
      refine ⟨83634838599286689751261795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111513118132382253001682393 83634838599286689751261795)
      ·
        refine ⟨125452257898930034626892693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83634838599286689751261795 125452257898930034626892693)
        ·
          refine ⟨5880574589012345373135595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 125452257898930034626892693 5880574589012345373135595)
          ·
            refine ⟨8820861883518518059703393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5880574589012345373135595 8820861883518518059703393)
            ·
              refine ⟨6615646412638888544777545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8820861883518518059703393 6615646412638888544777545)
              ·
                refine ⟨4961734809479166408583159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6615646412638888544777545 4961734809479166408583159)
                ·
                  refine ⟨7442602214218749612874739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4961734809479166408583159 7442602214218749612874739)
                  ·
                    refine ⟨11163903321328124419312109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7442602214218749612874739 11163903321328124419312109)
                    ·
                      refine ⟨4186463745498046657242041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11163903321328124419312109 4186463745498046657242041)
                      ·
                        rfl

theorem cell23_8153109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 2, 1, 1, 3].length) (baseStart_8153109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8153109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8153109 prefixEnd_8153109 := by exact prefixLift 8153109
  have htrace : WordTrace (prefixWord ++ tailWord_8153109) baseStart_8153109 baseEnd_8153109 := by
    simpa [prefixWord, tailWord_8153109, baseEnd_8153109] using wordTrace_append hprefix tailTrace_8153109
  have hstable : (prefixWord ++ tailWord_8153109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8153109).length < 2 ^ (prefixWord ++ tailWord_8153109).sum := by decide
  have hdescent : baseEnd_8153109 < baseStart_8153109 := by decide
  rcases family_descends (prefixWord ++ tailWord_8153109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8153121 : List Nat := [1, 2, 3, 2, 4, 2, 1, 8]
def baseStart_8153121 : Nat := 118140960795 + 8153121 * 2 ^ 59
def prefixEnd_8153121 : Nat := 4983230072969 + 3 ^ 40 * 8153121 * 2
def baseEnd_8153121 : Nat := 155054441009848170751555

theorem tailTrace_8153121 : CollatzResearch.WordTrace tailWord_8153121 prefixEnd_8153121 155054441009848170751555 := by
  unfold tailWord_8153121
  simp only [CollatzResearch.WordTrace]
  refine ⟨297368752695642534053923217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198245835130428356035948811 297368752695642534053923217)
  ·
    refine ⟨223026564521731900540442413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297368752695642534053923217 223026564521731900540442413)
    ·
      refine ⟨83634961695649462702665905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223026564521731900540442413 83634961695649462702665905)
      ·
        refine ⟨62726221271737097026999429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83634961695649462702665905 62726221271737097026999429)
        ·
          refine ⟨11761166488450705692562393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62726221271737097026999429 11761166488450705692562393)
          ·
            refine ⟨8820874866338029269421795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11761166488450705692562393 8820874866338029269421795)
            ·
              refine ⟨13231312299507043904132693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8820874866338029269421795 13231312299507043904132693)
              ·
                refine ⟨155054441009848170751555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13231312299507043904132693 155054441009848170751555)
                ·
                  rfl

theorem cell23_8153121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 8].length) (baseStart_8153121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8153121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8153121 prefixEnd_8153121 := by exact prefixLift 8153121
  have htrace : WordTrace (prefixWord ++ tailWord_8153121) baseStart_8153121 baseEnd_8153121 := by
    simpa [prefixWord, tailWord_8153121, baseEnd_8153121] using wordTrace_append hprefix tailTrace_8153121
  have hstable : (prefixWord ++ tailWord_8153121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8153121).length < 2 ^ (prefixWord ++ tailWord_8153121).sum := by decide
  have hdescent : baseEnd_8153121 < baseStart_8153121 := by decide
  rcases family_descends (prefixWord ++ tailWord_8153121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8153164 : List Nat := [2, 2, 1, 3, 1, 1, 3, 2, 2, 6]
def baseStart_8153164 : Nat := 118140960795 + 8153164 * 2 ^ 59
def prefixEnd_8153164 : Nat := 4983230072969 + 3 ^ 40 * 8153164 * 2
def baseEnd_8153164 : Nat := 1395497328978014647351429

theorem tailTrace_8153164 : CollatzResearch.WordTrace tailWord_8153164 prefixEnd_8153164 1395497328978014647351429 := by
  unfold tailWord_8153164
  simp only [CollatzResearch.WordTrace]
  refine ⟨148685160517243376198869273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198246880689657834931825697 148685160517243376198869273)
  ·
    refine ⟨111513870387932532149151955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148685160517243376198869273 111513870387932532149151955)
    ·
      refine ⟨167270805581898798223727933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111513870387932532149151955 167270805581898798223727933)
      ·
        refine ⟨62726552093212049333897975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167270805581898798223727933 62726552093212049333897975)
        ·
          refine ⟨94089828139818074000846963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62726552093212049333897975 94089828139818074000846963)
          ·
            refine ⟨141134742209727111001270445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94089828139818074000846963 141134742209727111001270445)
            ·
              refine ⟨52925528328647666625476417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141134742209727111001270445 52925528328647666625476417)
              ·
                refine ⟨39694146246485749969107313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52925528328647666625476417 39694146246485749969107313)
                ·
                  refine ⟨29770609684864312476830485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39694146246485749969107313 29770609684864312476830485)
                  ·
                    refine ⟨1395497328978014647351429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29770609684864312476830485 1395497328978014647351429)
                    ·
                      rfl

theorem cell23_8153164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 2, 6].length) (baseStart_8153164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8153164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8153164 prefixEnd_8153164 := by exact prefixLift 8153164
  have htrace : WordTrace (prefixWord ++ tailWord_8153164) baseStart_8153164 baseEnd_8153164 := by
    simpa [prefixWord, tailWord_8153164, baseEnd_8153164] using wordTrace_append hprefix tailTrace_8153164
  have hstable : (prefixWord ++ tailWord_8153164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8153164).length < 2 ^ (prefixWord ++ tailWord_8153164).sum := by decide
  have hdescent : baseEnd_8153164 < baseStart_8153164 := by decide
  rcases family_descends (prefixWord ++ tailWord_8153164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8153188 : List Nat := [2, 3, 1, 1, 2, 1, 5, 1, 1, 4, 2]
def baseStart_8153188 : Nat := 118140960795 + 8153188 * 2 ^ 59
def prefixEnd_8153188 : Nat := 4983230072969 + 3 ^ 40 * 8153188 * 2
def baseEnd_8153188 : Nat := 4186504310469751848154177

theorem tailTrace_8153188 : CollatzResearch.WordTrace tailWord_8153188 prefixEnd_8153188 4186504310469751848154177 := by
  unfold tailWord_8153188
  simp only [CollatzResearch.WordTrace]
  refine ⟨148685598193199902248306109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198247464257599869664408145 148685598193199902248306109)
  ·
    refine ⟨55757099322449963343114791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148685598193199902248306109 55757099322449963343114791)
    ·
      refine ⟨83635648983674945014672187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55757099322449963343114791 83635648983674945014672187)
      ·
        refine ⟨125453473475512417522008281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83635648983674945014672187 125453473475512417522008281)
        ·
          refine ⟨94090105106634313141506211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125453473475512417522008281 94090105106634313141506211)
          ·
            refine ⟨141135157659951469712259317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94090105106634313141506211 141135157659951469712259317)
            ·
              refine ⟨13231421030620450285524311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141135157659951469712259317 13231421030620450285524311)
              ·
                refine ⟨19847131545930675428286467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13231421030620450285524311 19847131545930675428286467)
                ·
                  refine ⟨29770697318896013142429701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19847131545930675428286467 29770697318896013142429701)
                  ·
                    refine ⟨5582005747293002464205569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29770697318896013142429701 5582005747293002464205569)
                    ·
                      refine ⟨4186504310469751848154177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5582005747293002464205569 4186504310469751848154177)
                      ·
                        rfl

theorem cell23_8153188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 1, 4, 2].length) (baseStart_8153188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8153188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8153188 prefixEnd_8153188 := by exact prefixLift 8153188
  have htrace : WordTrace (prefixWord ++ tailWord_8153188) baseStart_8153188 baseEnd_8153188 := by
    simpa [prefixWord, tailWord_8153188, baseEnd_8153188] using wordTrace_append hprefix tailTrace_8153188
  have hstable : (prefixWord ++ tailWord_8153188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8153188).length < 2 ^ (prefixWord ++ tailWord_8153188).sum := by decide
  have hdescent : baseEnd_8153188 < baseStart_8153188 := by decide
  rcases family_descends (prefixWord ++ tailWord_8153188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8153239 : List Nat := [1, 1, 3, 3, 4, 2, 2, 1, 2, 2, 2]
def baseStart_8153239 : Nat := 118140960795 + 8153239 * 2 ^ 59
def prefixEnd_8153239 : Nat := 4983230072969 + 3 ^ 40 * 8153239 * 2
def baseEnd_8153239 : Nat := 4186530497983131148616443

theorem tailTrace_8153239 : CollatzResearch.WordTrace tailWord_8153239 prefixEnd_8153239 4186530497983131148616443 := by
  unfold tailWord_8153239
  simp only [CollatzResearch.WordTrace]
  refine ⟨297373056509215040206718771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198248704339476693471145847 297373056509215040206718771)
  ·
    refine ⟨446059584763822560310078157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297373056509215040206718771 446059584763822560310078157)
    ·
      refine ⟨167272344286433460116279309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 446059584763822560310078157 167272344286433460116279309)
      ·
        refine ⟨62727129107412547543604741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167272344286433460116279309 62727129107412547543604741)
        ·
          refine ⟨11761336707639852664425889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62727129107412547543604741 11761336707639852664425889)
          ·
            refine ⟨8821002530729889498319417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11761336707639852664425889 8821002530729889498319417)
            ·
              refine ⟨6615751898047417123739563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8821002530729889498319417 6615751898047417123739563)
              ·
                refine ⟨9923627847071125685609345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6615751898047417123739563 9923627847071125685609345)
                ·
                  refine ⟨7442720885303344264207009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9923627847071125685609345 7442720885303344264207009)
                  ·
                    refine ⟨5582040663977508198155257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7442720885303344264207009 5582040663977508198155257)
                    ·
                      refine ⟨4186530497983131148616443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5582040663977508198155257 4186530497983131148616443)
                      ·
                        rfl

theorem cell23_8153239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 1, 2, 2, 2].length) (baseStart_8153239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8153239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8153239 prefixEnd_8153239 := by exact prefixLift 8153239
  have htrace : WordTrace (prefixWord ++ tailWord_8153239) baseStart_8153239 baseEnd_8153239 := by
    simpa [prefixWord, tailWord_8153239, baseEnd_8153239] using wordTrace_append hprefix tailTrace_8153239
  have hstable : (prefixWord ++ tailWord_8153239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8153239).length < 2 ^ (prefixWord ++ tailWord_8153239).sum := by decide
  have hdescent : baseEnd_8153239 < baseStart_8153239 := by decide
  rcases family_descends (prefixWord ++ tailWord_8153239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8153264 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 5]
def baseStart_8153264 : Nat := 118140960795 + 8153264 * 2 ^ 59
def prefixEnd_8153264 : Nat := 4983230072969 + 3 ^ 40 * 8153264 * 2
def baseEnd_8153264 : Nat := 4186543334999493550803827

theorem tailTrace_8153264 : CollatzResearch.WordTrace tailWord_8153264 prefixEnd_8153264 4186543334999493550803827 := by
  unfold tailWord_8153264
  simp only [CollatzResearch.WordTrace]
  refine ⟨148686984167062234738189423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198249312222749646317585897 148686984167062234738189423)
  ·
    refine ⟨223030476250593352107284135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148686984167062234738189423 223030476250593352107284135)
    ·
      refine ⟨334545714375890028160926203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223030476250593352107284135 334545714375890028160926203)
      ·
        refine ⟨501818571563835042241389305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334545714375890028160926203 501818571563835042241389305)
        ·
          refine ⟨376363928672876281681041979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 501818571563835042241389305 376363928672876281681041979)
          ·
            refine ⟨564545893009314422521562969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376363928672876281681041979 564545893009314422521562969)
            ·
              refine ⟨423409419756985816891172227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 564545893009314422521562969 423409419756985816891172227)
              ·
                refine ⟨635114129635478725336758341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 423409419756985816891172227 635114129635478725336758341)
                ·
                  refine ⟨119083899306652261000642189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 635114129635478725336758341 119083899306652261000642189)
                  ·
                    refine ⟨44656462239994597875240821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119083899306652261000642189 44656462239994597875240821)
                    ·
                      refine ⟨4186543334999493550803827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44656462239994597875240821 4186543334999493550803827)
                      ·
                        rfl

theorem cell23_8153264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 5].length) (baseStart_8153264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8153264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8153264 prefixEnd_8153264 := by exact prefixLift 8153264
  have htrace : WordTrace (prefixWord ++ tailWord_8153264) baseStart_8153264 baseEnd_8153264 := by
    simpa [prefixWord, tailWord_8153264, baseEnd_8153264] using wordTrace_append hprefix tailTrace_8153264
  have hstable : (prefixWord ++ tailWord_8153264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8153264).length < 2 ^ (prefixWord ++ tailWord_8153264).sum := by decide
  have hdescent : baseEnd_8153264 < baseStart_8153264 := by decide
  rcases family_descends (prefixWord ++ tailWord_8153264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8153282 : List Nat := [3, 5, 1, 1, 1, 1, 1, 1, 2, 5, 2]
def baseStart_8153282 : Nat := 118140960795 + 8153282 * 2 ^ 59
def prefixEnd_8153282 : Nat := 4983230072969 + 3 ^ 40 * 8153282 * 2
def baseEnd_8153282 : Nat := 4186552577651274480378745

theorem tailTrace_8153282 : CollatzResearch.WordTrace tailWord_8153282 prefixEnd_8153282 4186552577651274480378745 := by
  unfold tailWord_8153282
  simp only [CollatzResearch.WordTrace]
  refine ⟨74343656212014814637633525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198249749898706172367022733 74343656212014814637633525)
  ·
    refine ⟨6969717769876388872278143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74343656212014814637633525 6969717769876388872278143)
    ·
      refine ⟨10454576654814583308417215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6969717769876388872278143 10454576654814583308417215)
      ·
        refine ⟨15681864982221874962625823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10454576654814583308417215 15681864982221874962625823)
        ·
          refine ⟨23522797473332812443938735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15681864982221874962625823 23522797473332812443938735)
          ·
            refine ⟨35284196209999218665908103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23522797473332812443938735 35284196209999218665908103)
            ·
              refine ⟨52926294314998827998862155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35284196209999218665908103 52926294314998827998862155)
              ·
                refine ⟨79389441472498241998293233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52926294314998827998862155 79389441472498241998293233)
                ·
                  refine ⟨59542081104373681498719925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79389441472498241998293233 59542081104373681498719925)
                  ·
                    refine ⟨5582070103535032640504993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59542081104373681498719925 5582070103535032640504993)
                    ·
                      refine ⟨4186552577651274480378745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5582070103535032640504993 4186552577651274480378745)
                      ·
                        rfl

theorem cell23_8153282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_8153282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8153282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8153282 prefixEnd_8153282 := by exact prefixLift 8153282
  have htrace : WordTrace (prefixWord ++ tailWord_8153282) baseStart_8153282 baseEnd_8153282 := by
    simpa [prefixWord, tailWord_8153282, baseEnd_8153282] using wordTrace_append hprefix tailTrace_8153282
  have hstable : (prefixWord ++ tailWord_8153282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8153282).length < 2 ^ (prefixWord ++ tailWord_8153282).sum := by decide
  have hdescent : baseEnd_8153282 < baseStart_8153282 := by decide
  rcases family_descends (prefixWord ++ tailWord_8153282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8153315 : List Nat := [1, 1, 1, 8, 1, 1, 1, 1, 1, 4, 3]
def baseStart_8153315 : Nat := 118140960795 + 8153315 * 2 ^ 59
def prefixEnd_8153315 : Nat := 4983230072969 + 3 ^ 40 * 8153315 * 2
def baseEnd_8153315 : Nat := 4186569522512872851266093

theorem tailTrace_8153315 : CollatzResearch.WordTrace tailWord_8153315 prefixEnd_8153315 4186569522512872851266093 := by
  unfold tailWord_8153315
  simp only [CollatzResearch.WordTrace]
  refine ⟨297375828456939705186485399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198250552304626470124323599 297375828456939705186485399)
  ·
    refine ⟨446063742685409557779728099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297375828456939705186485399 446063742685409557779728099)
    ·
      refine ⟨669095614028114336669592149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446063742685409557779728099 669095614028114336669592149)
      ·
        refine ⟨7840964226891964882846783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 669095614028114336669592149 7840964226891964882846783)
        ·
          refine ⟨11761446340337947324270175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7840964226891964882846783 11761446340337947324270175)
          ·
            refine ⟨17642169510506920986405263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11761446340337947324270175 17642169510506920986405263)
            ·
              refine ⟨26463254265760381479607895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17642169510506920986405263 26463254265760381479607895)
              ·
                refine ⟨39694881398640572219411843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26463254265760381479607895 39694881398640572219411843)
                ·
                  refine ⟨59542322097960858329117765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39694881398640572219411843 59542322097960858329117765)
                  ·
                    refine ⟨11164185393367660936709581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59542322097960858329117765 11164185393367660936709581)
                    ·
                      refine ⟨4186569522512872851266093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11164185393367660936709581 4186569522512872851266093)
                      ·
                        rfl

theorem cell23_8153315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_8153315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8153315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8153315 prefixEnd_8153315 := by exact prefixLift 8153315
  have htrace : WordTrace (prefixWord ++ tailWord_8153315) baseStart_8153315 baseEnd_8153315 := by
    simpa [prefixWord, tailWord_8153315, baseEnd_8153315] using wordTrace_append hprefix tailTrace_8153315
  have hstable : (prefixWord ++ tailWord_8153315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8153315).length < 2 ^ (prefixWord ++ tailWord_8153315).sum := by decide
  have hdescent : baseEnd_8153315 < baseStart_8153315 := by decide
  rcases family_descends (prefixWord ++ tailWord_8153315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8153345 : List Nat := [1, 2, 4, 1, 1, 2, 4, 1, 3, 1, 3]
def baseStart_8153345 : Nat := 118140960795 + 8153345 * 2 ^ 59
def prefixEnd_8153345 : Nat := 4983230072969 + 3 ^ 40 * 8153345 * 2
def baseEnd_8153345 : Nat := 4186584926932507733890955

theorem tailTrace_8153345 : CollatzResearch.WordTrace tailWord_8153345 prefixEnd_8153345 4186584926932507733890955 := by
  unfold tailWord_8153345
  simp only [CollatzResearch.WordTrace]
  refine ⟨297376922646831020310077489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198251281764554013540051659 297376922646831020310077489)
  ·
    refine ⟨223032691985123265232558117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297376922646831020310077489 223032691985123265232558117)
    ·
      refine ⟨41818629747210612231104647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223032691985123265232558117 41818629747210612231104647)
      ·
        refine ⟨62727944620815918346656971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41818629747210612231104647 62727944620815918346656971)
        ·
          refine ⟨94091916931223877519985457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62727944620815918346656971 94091916931223877519985457)
          ·
            refine ⟨70568937698417908139989093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94091916931223877519985457 70568937698417908139989093)
            ·
              refine ⟨13231675818453357776247955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70568937698417908139989093 13231675818453357776247955)
              ·
                refine ⟨19847513727680036664371933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13231675818453357776247955 19847513727680036664371933)
                ·
                  refine ⟨7442817647880013749139475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19847513727680036664371933 7442817647880013749139475)
                  ·
                    refine ⟨11164226471820020623709213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7442817647880013749139475 11164226471820020623709213)
                    ·
                      refine ⟨4186584926932507733890955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11164226471820020623709213 4186584926932507733890955)
                      ·
                        rfl

theorem cell23_8153345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_8153345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8153345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8153345 prefixEnd_8153345 := by exact prefixLift 8153345
  have htrace : WordTrace (prefixWord ++ tailWord_8153345) baseStart_8153345 baseEnd_8153345 := by
    simpa [prefixWord, tailWord_8153345, baseEnd_8153345] using wordTrace_append hprefix tailTrace_8153345
  have hstable : (prefixWord ++ tailWord_8153345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8153345).length < 2 ^ (prefixWord ++ tailWord_8153345).sum := by decide
  have hdescent : baseEnd_8153345 < baseStart_8153345 := by decide
  rcases family_descends (prefixWord ++ tailWord_8153345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8153368 : List Nat := [2, 1, 2, 3, 1, 2, 1, 1, 2, 6, 2]
def baseStart_8153368 : Nat := 118140960795 + 8153368 * 2 ^ 59
def prefixEnd_8153368 : Nat := 4983230072969 + 3 ^ 40 * 8153368 * 2
def baseEnd_8153368 : Nat := 4186596736987561143903349

theorem tailTrace_8153368 : CollatzResearch.WordTrace tailWord_8153368 prefixEnd_8153368 4186596736987561143903349 := by
  unfold tailWord_8153368
  simp only [CollatzResearch.WordTrace]
  refine ⟨148688880762873847619082379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198251841017165130158776505 148688880762873847619082379)
  ·
    refine ⟨223033321144310771428623569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148688880762873847619082379 223033321144310771428623569)
    ·
      refine ⟨167274990858233078571467677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223033321144310771428623569 167274990858233078571467677)
      ·
        refine ⟨62728121571837404464300379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167274990858233078571467677 62728121571837404464300379)
        ·
          refine ⟨94092182357756106696450569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62728121571837404464300379 94092182357756106696450569)
          ·
            refine ⟨70569136768317080022337927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94092182357756106696450569 70569136768317080022337927)
            ·
              refine ⟨105853705152475620033506891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70569136768317080022337927 105853705152475620033506891)
              ·
                refine ⟨158780557728713430050260337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105853705152475620033506891 158780557728713430050260337)
                ·
                  refine ⟨119085418296535072537695253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158780557728713430050260337 119085418296535072537695253)
                  ·
                    refine ⟨5582128982650081525204465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 119085418296535072537695253 5582128982650081525204465)
                    ·
                      refine ⟨4186596736987561143903349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5582128982650081525204465 4186596736987561143903349)
                      ·
                        rfl

theorem cell23_8153368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 2, 6, 2].length) (baseStart_8153368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8153368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8153368 prefixEnd_8153368 := by exact prefixLift 8153368
  have htrace : WordTrace (prefixWord ++ tailWord_8153368) baseStart_8153368 baseEnd_8153368 := by
    simpa [prefixWord, tailWord_8153368, baseEnd_8153368] using wordTrace_append hprefix tailTrace_8153368
  have hstable : (prefixWord ++ tailWord_8153368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8153368).length < 2 ^ (prefixWord ++ tailWord_8153368).sum := by decide
  have hdescent : baseEnd_8153368 < baseStart_8153368 := by decide
  rcases family_descends (prefixWord ++ tailWord_8153368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8153389 : List Nat := [1, 5, 3, 1, 2, 1, 1, 2, 2, 3, 2]
def baseStart_8153389 : Nat := 118140960795 + 8153389 * 2 ^ 59
def prefixEnd_8153389 : Nat := 4983230072969 + 3 ^ 40 * 8153389 * 2
def baseEnd_8153389 : Nat := 4186607520081305561740753

theorem tailTrace_8153389 : CollatzResearch.WordTrace tailWord_8153389 prefixEnd_8153389 4186607520081305561740753 := by
  unfold tailWord_8153389
  simp only [CollatzResearch.WordTrace]
  refine ⟨297378527458671615824679221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198252351639114410549786147 297378527458671615824679221)
  ·
    refine ⟨27879236949250463983563677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 297378527458671615824679221 27879236949250463983563677)
    ·
      refine ⟨10454713855968923993836379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27879236949250463983563677 10454713855968923993836379)
      ·
        refine ⟨15682070783953385990754569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10454713855968923993836379 15682070783953385990754569)
        ·
          refine ⟨11761553087965039493065927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15682070783953385990754569 11761553087965039493065927)
          ·
            refine ⟨17642329631947559239598891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11761553087965039493065927 17642329631947559239598891)
            ·
              refine ⟨26463494447921338859398337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17642329631947559239598891 26463494447921338859398337)
              ·
                refine ⟨19847620835941004144548753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26463494447921338859398337 19847620835941004144548753)
                ·
                  refine ⟨14885715626955753108411565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19847620835941004144548753 14885715626955753108411565)
                  ·
                    refine ⟨5582143360108407415654337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14885715626955753108411565 5582143360108407415654337)
                    ·
                      refine ⟨4186607520081305561740753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5582143360108407415654337 4186607520081305561740753)
                      ·
                        rfl

theorem cell23_8153389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_8153389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8153389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8153389 prefixEnd_8153389 := by exact prefixLift 8153389
  have htrace : WordTrace (prefixWord ++ tailWord_8153389) baseStart_8153389 baseEnd_8153389 := by
    simpa [prefixWord, tailWord_8153389, baseEnd_8153389] using wordTrace_append hprefix tailTrace_8153389
  have hstable : (prefixWord ++ tailWord_8153389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8153389).length < 2 ^ (prefixWord ++ tailWord_8153389).sum := by decide
  have hdescent : baseEnd_8153389 < baseStart_8153389 := by decide
  rcases family_descends (prefixWord ++ tailWord_8153389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8153396 : List Nat := [2, 5, 1, 1, 1, 3, 3, 2, 1, 1, 3]
def baseStart_8153396 : Nat := 118140960795 + 8153396 * 2 ^ 59
def prefixEnd_8153396 : Nat := 4983230072969 + 3 ^ 40 * 8153396 * 2
def baseEnd_8153396 : Nat := 4186611114445887034353221

theorem tailTrace_8153396 : CollatzResearch.WordTrace tailWord_8153396 prefixEnd_8153396 4186611114445887034353221 := by
  unfold tailWord_8153396
  simp only [CollatzResearch.WordTrace]
  refine ⟨148689391384823128010092021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198252521846430837346789361 148689391384823128010092021)
  ·
    refine ⟨13939630442327168250946127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148689391384823128010092021 13939630442327168250946127)
    ·
      refine ⟨20909445663490752376419191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13939630442327168250946127 20909445663490752376419191)
      ·
        refine ⟨31364168495236128564628787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20909445663490752376419191 31364168495236128564628787)
        ·
          refine ⟨47046252742854192846943181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31364168495236128564628787 47046252742854192846943181)
          ·
            refine ⟨17642344778570322317603693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47046252742854192846943181 17642344778570322317603693)
            ·
              refine ⟨6615879291963870869101385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17642344778570322317603693 6615879291963870869101385)
              ·
                refine ⟨4961909468972903151826039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6615879291963870869101385 4961909468972903151826039)
                ·
                  refine ⟨7442864203459354727739059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4961909468972903151826039 7442864203459354727739059)
                  ·
                    refine ⟨11164296305189032091608589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7442864203459354727739059 11164296305189032091608589)
                    ·
                      refine ⟨4186611114445887034353221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11164296305189032091608589 4186611114445887034353221)
                      ·
                        rfl

theorem cell23_8153396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_8153396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8153396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8153396 prefixEnd_8153396 := by exact prefixLift 8153396
  have htrace : WordTrace (prefixWord ++ tailWord_8153396) baseStart_8153396 baseEnd_8153396 := by
    simpa [prefixWord, tailWord_8153396, baseEnd_8153396] using wordTrace_append hprefix tailTrace_8153396
  have hstable : (prefixWord ++ tailWord_8153396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8153396).length < 2 ^ (prefixWord ++ tailWord_8153396).sum := by decide
  have hdescent : baseEnd_8153396 < baseStart_8153396 := by decide
  rcases family_descends (prefixWord ++ tailWord_8153396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8153402 : List Nat := [3, 1, 1, 1, 4, 2, 3, 1, 3, 2, 2]
def baseStart_8153402 : Nat := 118140960795 + 8153402 * 2 ^ 59
def prefixEnd_8153402 : Nat := 4983230072969 + 3 ^ 40 * 8153402 * 2
def baseEnd_8153402 : Nat := 4186614195329814010878193

theorem tailTrace_8153402 : CollatzResearch.WordTrace tailWord_8153402 prefixEnd_8153402 4186614195329814010878193 := by
  unfold tailWord_8153402
  simp only [CollatzResearch.WordTrace]
  refine ⟨74344750401906129761225615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198252667738416346029934973 74344750401906129761225615)
  ·
    refine ⟨111517125602859194641838423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74344750401906129761225615 111517125602859194641838423)
    ·
      refine ⟨167275688404288791962757635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111517125602859194641838423 167275688404288791962757635)
      ·
        refine ⟨250913532606433187944136453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167275688404288791962757635 250913532606433187944136453)
        ·
          refine ⟨47046287363706222739525585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 250913532606433187944136453 47046287363706222739525585)
          ·
            refine ⟨35284715522779667054644189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47046287363706222739525585 35284715522779667054644189)
            ·
              refine ⟨13231768321042375145491571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35284715522779667054644189 13231768321042375145491571)
              ·
                refine ⟨19847652481563562718237357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13231768321042375145491571 19847652481563562718237357)
                ·
                  refine ⟨7442869680586336019339009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19847652481563562718237357 7442869680586336019339009)
                  ·
                    refine ⟨5582152260439752014504257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7442869680586336019339009 5582152260439752014504257)
                    ·
                      refine ⟨4186614195329814010878193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5582152260439752014504257 4186614195329814010878193)
                      ·
                        rfl

theorem cell23_8153402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 3, 2, 2].length) (baseStart_8153402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8153402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8153402 prefixEnd_8153402 := by exact prefixLift 8153402
  have htrace : WordTrace (prefixWord ++ tailWord_8153402) baseStart_8153402 baseEnd_8153402 := by
    simpa [prefixWord, tailWord_8153402, baseEnd_8153402] using wordTrace_append hprefix tailTrace_8153402
  have hstable : (prefixWord ++ tailWord_8153402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8153402).length < 2 ^ (prefixWord ++ tailWord_8153402).sum := by decide
  have hdescent : baseEnd_8153402 < baseStart_8153402 := by decide
  rcases family_descends (prefixWord ++ tailWord_8153402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8153451 : List Nat := [1, 1, 1, 1, 2, 2, 2, 3, 4, 6]
def baseStart_8153451 : Nat := 118140960795 + 8153451 * 2 ^ 59
def prefixEnd_8153451 : Nat := 4983230072969 + 3 ^ 40 * 8153451 * 2
def baseEnd_8153451 : Nat := 1395546451960628106388489

theorem tailTrace_8153451 : CollatzResearch.WordTrace tailWord_8153451 prefixEnd_8153451 1395546451960628106388489 := by
  unfold tailWord_8153451
  simp only [CollatzResearch.WordTrace]
  refine ⟨297380788784447000413436207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198253859189631333608957471 297380788784447000413436207)
  ·
    refine ⟨446071183176670500620154311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297380788784447000413436207 446071183176670500620154311)
    ·
      refine ⟨669106774765005750930231467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446071183176670500620154311 669106774765005750930231467)
      ·
        refine ⟨1003660162147508626395347201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 669106774765005750930231467 1003660162147508626395347201)
        ·
          refine ⟨752745121610631469796510401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1003660162147508626395347201 752745121610631469796510401)
          ·
            refine ⟨564558841207973602347382801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 752745121610631469796510401 564558841207973602347382801)
            ·
              refine ⟨423419130905980201760537101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 564558841207973602347382801 423419130905980201760537101)
              ·
                refine ⟨158782174089742575660201413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 423419130905980201760537101 158782174089742575660201413)
                ·
                  refine ⟨29771657641826732936287765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158782174089742575660201413 29771657641826732936287765)
                  ·
                    refine ⟨1395546451960628106388489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29771657641826732936287765 1395546451960628106388489)
                    ·
                      rfl

theorem cell23_8153451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 6].length) (baseStart_8153451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8153451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8153451 prefixEnd_8153451 := by exact prefixLift 8153451
  have htrace : WordTrace (prefixWord ++ tailWord_8153451) baseStart_8153451 baseEnd_8153451 := by
    simpa [prefixWord, tailWord_8153451, baseEnd_8153451] using wordTrace_append hprefix tailTrace_8153451
  have hstable : (prefixWord ++ tailWord_8153451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8153451).length < 2 ^ (prefixWord ++ tailWord_8153451).sum := by decide
  have hdescent : baseEnd_8153451 < baseStart_8153451 := by decide
  rcases family_descends (prefixWord ++ tailWord_8153451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8153458 : List Nat := [3, 2, 1, 2, 1, 3, 1, 1, 2, 3, 4]
def baseStart_8153458 : Nat := 118140960795 + 8153458 * 2 ^ 59
def prefixEnd_8153458 : Nat := 4983230072969 + 3 ^ 40 * 8153458 * 2
def baseEnd_8153458 : Nat := 4186642950246465791777935

theorem tailTrace_8153458 : CollatzResearch.WordTrace tailWord_8153458 prefixEnd_8153458 4186642950246465791777935 := by
  unfold tailWord_8153458
  simp only [CollatzResearch.WordTrace]
  refine ⟨74345261023855410152235257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198254029396947760405960685 74345261023855410152235257)
  ·
    refine ⟨55758945767891557614176443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74345261023855410152235257 55758945767891557614176443)
    ·
      refine ⟨83638418651837336421264665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55758945767891557614176443 83638418651837336421264665)
      ·
        refine ⟨62728813988878002315948499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83638418651837336421264665 62728813988878002315948499)
        ·
          refine ⟨94093220983317003473922749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62728813988878002315948499 94093220983317003473922749)
          ·
            refine ⟨35284957868743876302721031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94093220983317003473922749 35284957868743876302721031)
            ·
              refine ⟨52927436803115814454081547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35284957868743876302721031 52927436803115814454081547)
              ·
                refine ⟨79391155204673721681122321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52927436803115814454081547 79391155204673721681122321)
                ·
                  refine ⟨59543366403505291260841741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79391155204673721681122321 59543366403505291260841741)
                  ·
                    refine ⟨22328762401314484222815653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59543366403505291260841741 22328762401314484222815653)
                    ·
                      refine ⟨4186642950246465791777935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22328762401314484222815653 4186642950246465791777935)
                      ·
                        rfl

theorem cell23_8153458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_8153458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8153458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8153458 prefixEnd_8153458 := by exact prefixLift 8153458
  have htrace : WordTrace (prefixWord ++ tailWord_8153458) baseStart_8153458 baseEnd_8153458 := by
    simpa [prefixWord, tailWord_8153458, baseEnd_8153458] using wordTrace_append hprefix tailTrace_8153458
  have hstable : (prefixWord ++ tailWord_8153458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8153458).length < 2 ^ (prefixWord ++ tailWord_8153458).sum := by decide
  have hdescent : baseEnd_8153458 < baseStart_8153458 := by decide
  rcases family_descends (prefixWord ++ tailWord_8153458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8153471 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 6]
def baseStart_8153471 : Nat := 118140960795 + 8153471 * 2 ^ 59
def prefixEnd_8153471 : Nat := 4983230072969 + 3 ^ 40 * 8153471 * 2
def baseEnd_8153471 : Nat := 4186649625494974240915375

theorem tailTrace_8153471 : CollatzResearch.WordTrace tailWord_8153471 prefixEnd_8153471 4186649625494974240915375 := by
  unfold tailWord_8153471
  simp only [CollatzResearch.WordTrace]
  refine ⟨297381518244374543829164267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198254345496249695886109511 297381518244374543829164267)
  ·
    refine ⟨446072277366561815743746401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297381518244374543829164267 446072277366561815743746401)
    ·
      refine ⟨334554208024921361807809801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446072277366561815743746401 334554208024921361807809801)
      ·
        refine ⟨250915656018691021355857351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334554208024921361807809801 250915656018691021355857351)
        ·
          refine ⟨376373484028036532033786027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250915656018691021355857351 376373484028036532033786027)
          ·
            refine ⟨564560226042054798050679041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376373484028036532033786027 564560226042054798050679041)
            ·
              refine ⟨423420169531541098538009281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 564560226042054798050679041 423420169531541098538009281)
              ·
                refine ⟨317565127148655823903506961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 423420169531541098538009281 317565127148655823903506961)
                ·
                  refine ⟨238173845361491867927630221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 317565127148655823903506961 238173845361491867927630221)
                  ·
                    refine ⟨89315192010559450472861333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 238173845361491867927630221 89315192010559450472861333)
                    ·
                      refine ⟨4186649625494974240915375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89315192010559450472861333 4186649625494974240915375)
                      ·
                        rfl

theorem cell23_8153471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 6].length) (baseStart_8153471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8153471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8153471 prefixEnd_8153471 := by exact prefixLift 8153471
  have htrace : WordTrace (prefixWord ++ tailWord_8153471) baseStart_8153471 baseEnd_8153471 := by
    simpa [prefixWord, tailWord_8153471, baseEnd_8153471] using wordTrace_append hprefix tailTrace_8153471
  have hstable : (prefixWord ++ tailWord_8153471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8153471).length < 2 ^ (prefixWord ++ tailWord_8153471).sum := by decide
  have hdescent : baseEnd_8153471 < baseStart_8153471 := by decide
  rcases family_descends (prefixWord ++ tailWord_8153471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8153496 : List Nat := [2, 1, 2, 5, 1, 3, 2, 1, 1, 3, 2]
def baseStart_8153496 : Nat := 118140960795 + 8153496 * 2 ^ 59
def prefixEnd_8153496 : Nat := 4983230072969 + 3 ^ 40 * 8153496 * 2
def baseEnd_8153496 : Nat := 4186662462511336643102761

theorem tailTrace_8153496 : CollatzResearch.WordTrace tailWord_8153496 prefixEnd_8153496 4186662462511336643102761 := by
  unfold tailWord_8153496
  simp only [CollatzResearch.WordTrace]
  refine ⟨148691215034641986549412171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198254953379522648732549561 148691215034641986549412171)
  ·
    refine ⟨223036822551962979824118257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148691215034641986549412171 223036822551962979824118257)
    ·
      refine ⟨167277616913972234868088693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223036822551962979824118257 167277616913972234868088693)
      ·
        refine ⟨15682276585684897018883315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 167277616913972234868088693 15682276585684897018883315)
        ·
          refine ⟨23523414878527345528324973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15682276585684897018883315 23523414878527345528324973)
          ·
            refine ⟨8821280579447754573121865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23523414878527345528324973 8821280579447754573121865)
            ·
              refine ⟨6615960434585815929841399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8821280579447754573121865 6615960434585815929841399)
              ·
                refine ⟨9923940651878723894762099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6615960434585815929841399 9923940651878723894762099)
                ·
                  refine ⟨14885910977818085842143149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9923940651878723894762099 14885910977818085842143149)
                  ·
                    refine ⟨5582216616681782190803681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14885910977818085842143149 5582216616681782190803681)
                    ·
                      refine ⟨4186662462511336643102761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5582216616681782190803681 4186662462511336643102761)
                      ·
                        rfl

theorem cell23_8153496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_8153496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8153496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8153496 prefixEnd_8153496 := by exact prefixLift 8153496
  have htrace : WordTrace (prefixWord ++ tailWord_8153496) baseStart_8153496 baseEnd_8153496 := by
    simpa [prefixWord, tailWord_8153496, baseEnd_8153496] using wordTrace_append hprefix tailTrace_8153496
  have hstable : (prefixWord ++ tailWord_8153496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8153496).length < 2 ^ (prefixWord ++ tailWord_8153496).sum := by decide
  have hdescent : baseEnd_8153496 < baseStart_8153496 := by decide
  rcases family_descends (prefixWord ++ tailWord_8153496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8153585 : List Nat := [1, 2, 2, 2, 3, 1, 1, 2, 4, 2, 3]
def baseStart_8153585 : Nat := 118140960795 + 8153585 * 2 ^ 59
def prefixEnd_8153585 : Nat := 4983230072969 + 3 ^ 40 * 8153585 * 2
def baseEnd_8153585 : Nat := 4186708162289586794889851

theorem tailTrace_8153585 : CollatzResearch.WordTrace tailWord_8153585 prefixEnd_8153585 4186708162289586794889851 := by
  unfold tailWord_8153585
  simp only [CollatzResearch.WordTrace]
  refine ⟨297385676165961541298814209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198257117443974360865876139 297385676165961541298814209)
  ·
    refine ⟨223039257124471155974110657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297385676165961541298814209 223039257124471155974110657)
    ·
      refine ⟨167279442843353366980582993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223039257124471155974110657 167279442843353366980582993)
      ·
        refine ⟨125459582132515025235437245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167279442843353366980582993 125459582132515025235437245)
        ·
          refine ⟨47047343299693134463288967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125459582132515025235437245 47047343299693134463288967)
          ·
            refine ⟨70571014949539701694933451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47047343299693134463288967 70571014949539701694933451)
            ·
              refine ⟨105856522424309552542400177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70571014949539701694933451 105856522424309552542400177)
              ·
                refine ⟨79392391818232164406800133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105856522424309552542400177 79392391818232164406800133)
                ·
                  refine ⟨14886073465918530826275025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79392391818232164406800133 14886073465918530826275025)
                  ·
                    refine ⟨11164555099438898119706269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14886073465918530826275025 11164555099438898119706269)
                    ·
                      refine ⟨4186708162289586794889851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11164555099438898119706269 4186708162289586794889851)
                      ·
                        rfl

theorem cell23_8153585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 4, 2, 3].length) (baseStart_8153585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8153585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8153585 prefixEnd_8153585 := by exact prefixLift 8153585
  have htrace : WordTrace (prefixWord ++ tailWord_8153585) baseStart_8153585 baseEnd_8153585 := by
    simpa [prefixWord, tailWord_8153585, baseEnd_8153585] using wordTrace_append hprefix tailTrace_8153585
  have hstable : (prefixWord ++ tailWord_8153585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8153585).length < 2 ^ (prefixWord ++ tailWord_8153585).sum := by decide
  have hdescent : baseEnd_8153585 < baseStart_8153585 := by decide
  rcases family_descends (prefixWord ++ tailWord_8153585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8153608 : List Nat := [2, 1, 3, 2, 1, 1, 1, 2, 1, 1, 8]
def baseStart_8153608 : Nat := 118140960795 + 8153608 * 2 ^ 59
def prefixEnd_8153608 : Nat := 4983230072969 + 3 ^ 40 * 8153608 * 2
def baseEnd_8153608 : Nat := 4186719972344640204902245

theorem tailTrace_8153608 : CollatzResearch.WordTrace tailWord_8153608 prefixEnd_8153608 4186719972344640204902245 := by
  unfold tailWord_8153608
  simp only [CollatzResearch.WordTrace]
  refine ⟨148693257522439108113450739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198257676696585477484600985 148693257522439108113450739)
  ·
    refine ⟨223039886283658662170176109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148693257522439108113450739 223039886283658662170176109)
    ·
      refine ⟨83639957356371998313816041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223039886283658662170176109 83639957356371998313816041)
      ·
        refine ⟨62729968017278998735362031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83639957356371998313816041 62729968017278998735362031)
        ·
          refine ⟨94094952025918498103043047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62729968017278998735362031 94094952025918498103043047)
          ·
            refine ⟨141142428038877747154564571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94094952025918498103043047 141142428038877747154564571)
            ·
              refine ⟨211713642058316620731846857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141142428038877747154564571 211713642058316620731846857)
              ·
                refine ⟨158785231543737465548885143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211713642058316620731846857 158785231543737465548885143)
                ·
                  refine ⟨238177847315606198323327715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158785231543737465548885143 238177847315606198323327715)
                  ·
                    refine ⟨357266770973409297484991573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 238177847315606198323327715 357266770973409297484991573)
                    ·
                      refine ⟨4186719972344640204902245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 357266770973409297484991573 4186719972344640204902245)
                      ·
                        rfl

theorem cell23_8153608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_8153608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8153608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8153608 prefixEnd_8153608 := by exact prefixLift 8153608
  have htrace : WordTrace (prefixWord ++ tailWord_8153608) baseStart_8153608 baseEnd_8153608 := by
    simpa [prefixWord, tailWord_8153608, baseEnd_8153608] using wordTrace_append hprefix tailTrace_8153608
  have hstable : (prefixWord ++ tailWord_8153608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8153608).length < 2 ^ (prefixWord ++ tailWord_8153608).sum := by decide
  have hdescent : baseEnd_8153608 < baseStart_8153608 := by decide
  rcases family_descends (prefixWord ++ tailWord_8153608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8153635 : List Nat := [1, 1, 1, 4, 4, 1, 1, 2, 3, 5]
def baseStart_8153635 : Nat := 118140960795 + 8153635 * 2 ^ 59
def prefixEnd_8153635 : Nat := 4983230072969 + 3 ^ 40 * 8153635 * 2
def baseEnd_8153635 : Nat := 1395577945440770533088207

theorem tailTrace_8153635 : CollatzResearch.WordTrace tailWord_8153635 prefixEnd_8153635 1395577945440770533088207 := by
  unfold tailWord_8153635
  simp only [CollatzResearch.WordTrace]
  refine ⟨297387499815780399838134359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198258333210520266558756239 297387499815780399838134359)
  ·
    refine ⟨446081249723670599757201539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297387499815780399838134359 446081249723670599757201539)
    ·
      refine ⟨669121874585505899635802309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446081249723670599757201539 669121874585505899635802309)
      ·
        refine ⟨125460351484782356181712933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 669121874585505899635802309 125460351484782356181712933)
        ·
          refine ⟨23523815903396691784071175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125460351484782356181712933 23523815903396691784071175)
          ·
            refine ⟨35285723855095037676106763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23523815903396691784071175 35285723855095037676106763)
            ·
              refine ⟨52928585782642556514160145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35285723855095037676106763 52928585782642556514160145)
              ·
                refine ⟨39696439336981917385620109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52928585782642556514160145 39696439336981917385620109)
                ·
                  refine ⟨14886164751368219019607541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39696439336981917385620109 14886164751368219019607541)
                  ·
                    refine ⟨1395577945440770533088207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14886164751368219019607541 1395577945440770533088207)
                    ·
                      rfl

theorem cell23_8153635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 3, 5].length) (baseStart_8153635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8153635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8153635 prefixEnd_8153635 := by exact prefixLift 8153635
  have htrace : WordTrace (prefixWord ++ tailWord_8153635) baseStart_8153635 baseEnd_8153635 := by
    simpa [prefixWord, tailWord_8153635, baseEnd_8153635] using wordTrace_append hprefix tailTrace_8153635
  have hstable : (prefixWord ++ tailWord_8153635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8153635).length < 2 ^ (prefixWord ++ tailWord_8153635).sum := by decide
  have hdescent : baseEnd_8153635 < baseStart_8153635 := by decide
  rcases family_descends (prefixWord ++ tailWord_8153635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8153655 : List Nat := [1, 1, 3, 1, 2, 3, 1, 3, 3, 1, 4]
def baseStart_8153655 : Nat := 118140960795 + 8153655 * 2 ^ 59
def prefixEnd_8153655 : Nat := 4983230072969 + 3 ^ 40 * 8153655 * 2
def baseEnd_8153655 : Nat := 4186744105935401521014529

theorem tailTrace_8153655 : CollatzResearch.WordTrace tailWord_8153655 prefixEnd_8153655 4186744105935401521014529 := by
  unfold tailWord_8153655
  simp only [CollatzResearch.WordTrace]
  refine ⟨297388229275707943253862419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198258819517138628835908279 297388229275707943253862419)
  ·
    refine ⟨446082343913561914880793629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297388229275707943253862419 446082343913561914880793629)
    ·
      refine ⟨167280878967585718080297611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 446082343913561914880793629 167280878967585718080297611)
      ·
        refine ⟨250921318451378577120446417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167280878967585718080297611 250921318451378577120446417)
        ·
          refine ⟨188190988838533932840334813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250921318451378577120446417 188190988838533932840334813)
          ·
            refine ⟨70571620814450224815125555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188190988838533932840334813 70571620814450224815125555)
            ·
              refine ⟨105857431221675337222688333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70571620814450224815125555 105857431221675337222688333)
              ·
                refine ⟨39696536708128251458508125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105857431221675337222688333 39696536708128251458508125)
                ·
                  refine ⟨14886201265548094296940547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39696536708128251458508125 14886201265548094296940547)
                  ·
                    refine ⟨22329301898322141445410821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14886201265548094296940547 22329301898322141445410821)
                    ·
                      refine ⟨4186744105935401521014529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22329301898322141445410821 4186744105935401521014529)
                      ·
                        rfl

theorem cell23_8153655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 3, 1, 4].length) (baseStart_8153655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8153655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8153655 prefixEnd_8153655 := by exact prefixLift 8153655
  have htrace : WordTrace (prefixWord ++ tailWord_8153655) baseStart_8153655 baseEnd_8153655 := by
    simpa [prefixWord, tailWord_8153655, baseEnd_8153655] using wordTrace_append hprefix tailTrace_8153655
  have hstable : (prefixWord ++ tailWord_8153655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8153655).length < 2 ^ (prefixWord ++ tailWord_8153655).sum := by decide
  have hdescent : baseEnd_8153655 < baseStart_8153655 := by decide
  rcases family_descends (prefixWord ++ tailWord_8153655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8153669 : List Nat := [1, 3, 1, 1, 1, 7, 2, 1, 1, 5]
def baseStart_8153669 : Nat := 118140960795 + 8153669 * 2 ^ 59
def prefixEnd_8153669 : Nat := 4983230072969 + 3 ^ 40 * 8153669 * 2
def baseEnd_8153669 : Nat := 1395583764888188155413155

theorem tailTrace_8153669 : CollatzResearch.WordTrace tailWord_8153669 prefixEnd_8153669 1395583764888188155413155 := by
  unfold tailWord_8153669
  simp only [CollatzResearch.WordTrace]
  refine ⟨297388739897657223644872061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198259159931771482429914707 297388739897657223644872061)
  ·
    refine ⟨111520777461621458866827023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297388739897657223644872061 111520777461621458866827023)
    ·
      refine ⟨167281166192432188300240535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111520777461621458866827023 167281166192432188300240535)
      ·
        refine ⟨250921749288648282450360803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167281166192432188300240535 250921749288648282450360803)
        ·
          refine ⟨376382623932972423675541205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250921749288648282450360803 376382623932972423675541205)
          ·
            refine ⟨8821467748429041179895497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 376382623932972423675541205 8821467748429041179895497)
            ·
              refine ⟨6616100811321780884921623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8821467748429041179895497 6616100811321780884921623)
              ·
                refine ⟨9924151216982671327382435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6616100811321780884921623 9924151216982671327382435)
                ·
                  refine ⟨14886226825474006991073653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9924151216982671327382435 14886226825474006991073653)
                  ·
                    refine ⟨1395583764888188155413155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14886226825474006991073653 1395583764888188155413155)
                    ·
                      rfl

theorem cell23_8153669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 1, 1, 5].length) (baseStart_8153669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8153669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8153669 prefixEnd_8153669 := by exact prefixLift 8153669
  have htrace : WordTrace (prefixWord ++ tailWord_8153669) baseStart_8153669 baseEnd_8153669 := by
    simpa [prefixWord, tailWord_8153669, baseEnd_8153669] using wordTrace_append hprefix tailTrace_8153669
  have hstable : (prefixWord ++ tailWord_8153669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8153669).length < 2 ^ (prefixWord ++ tailWord_8153669).sum := by decide
  have hdescent : baseEnd_8153669 < baseStart_8153669 := by decide
  rcases family_descends (prefixWord ++ tailWord_8153669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8153682 : List Nat := [3, 2, 2, 1, 2, 1, 3, 1, 4, 4]
def baseStart_8153682 : Nat := 118140960795 + 8153682 * 2 ^ 59
def prefixEnd_8153682 : Nat := 4983230072969 + 3 ^ 40 * 8153682 * 2
def baseEnd_8153682 : Nat := 1395585989971024305125635

theorem tailTrace_8153682 : CollatzResearch.WordTrace tailWord_8153682 prefixEnd_8153682 1395585989971024305125635 := by
  unfold tailWord_8153682
  simp only [CollatzResearch.WordTrace]
  refine ⟨74347303511652531716273825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198259476031073417910063533 74347303511652531716273825)
  ·
    refine ⟨55760477633739398787205369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74347303511652531716273825 55760477633739398787205369)
    ·
      refine ⟨41820358225304549090404027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55760477633739398787205369 41820358225304549090404027)
      ·
        refine ⟨62730537337956823635606041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41820358225304549090404027 62730537337956823635606041)
        ·
          refine ⟨47047903003467617726704531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62730537337956823635606041 47047903003467617726704531)
          ·
            refine ⟨70571854505201426590056797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47047903003467617726704531 70571854505201426590056797)
            ·
              refine ⟨26464445439450534971271299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70571854505201426590056797 26464445439450534971271299)
              ·
                refine ⟨39696668159175802456906949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26464445439450534971271299 39696668159175802456906949)
                ·
                  refine ⟨7443125279845462960670053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39696668159175802456906949 7443125279845462960670053)
                  ·
                    refine ⟨1395585989971024305125635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7443125279845462960670053 1395585989971024305125635)
                    ·
                      rfl

theorem cell23_8153682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_8153682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8153682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8153682 prefixEnd_8153682 := by exact prefixLift 8153682
  have htrace : WordTrace (prefixWord ++ tailWord_8153682) baseStart_8153682 baseEnd_8153682 := by
    simpa [prefixWord, tailWord_8153682, baseEnd_8153682] using wordTrace_append hprefix tailTrace_8153682
  have hstable : (prefixWord ++ tailWord_8153682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8153682).length < 2 ^ (prefixWord ++ tailWord_8153682).sum := by decide
  have hdescent : baseEnd_8153682 < baseStart_8153682 := by decide
  rcases family_descends (prefixWord ++ tailWord_8153682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8153685 : List Nat := [1, 3, 2, 2, 1, 1, 2, 2, 3, 2, 4]
def baseStart_8153685 : Nat := 118140960795 + 8153685 * 2 ^ 59
def prefixEnd_8153685 : Nat := 4983230072969 + 3 ^ 40 * 8153685 * 2
def baseEnd_8153685 : Nat := 4186759510355036403639391

theorem tailTrace_8153685 : CollatzResearch.WordTrace tailWord_8153685 prefixEnd_8153685 4186759510355036403639391 := by
  unfold tailWord_8153685
  simp only [CollatzResearch.WordTrace]
  refine ⟨297389323465599258377454509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198259548977066172251636339 297389323465599258377454509)
  ·
    refine ⟨111520996299599721891545441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297389323465599258377454509 111520996299599721891545441)
    ·
      refine ⟨83640747224699791418659081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111520996299599721891545441 83640747224699791418659081)
      ·
        refine ⟨62730560418524843563994311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83640747224699791418659081 62730560418524843563994311)
        ·
          refine ⟨94095840627787265345991467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62730560418524843563994311 94095840627787265345991467)
          ·
            refine ⟨141143760941680898018987201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94095840627787265345991467 141143760941680898018987201)
            ·
              refine ⟨105857820706260673514240401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141143760941680898018987201 105857820706260673514240401)
              ·
                refine ⟨79393365529695505135680301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105857820706260673514240401 79393365529695505135680301)
                ·
                  refine ⟨29772512073635814425880113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79393365529695505135680301 29772512073635814425880113)
                  ·
                    refine ⟨22329384055226860819410085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29772512073635814425880113 22329384055226860819410085)
                    ·
                      refine ⟨4186759510355036403639391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22329384055226860819410085 4186759510355036403639391)
                      ·
                        rfl

theorem cell23_8153685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_8153685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8153685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8153685 prefixEnd_8153685 := by exact prefixLift 8153685
  have htrace : WordTrace (prefixWord ++ tailWord_8153685) baseStart_8153685 baseEnd_8153685 := by
    simpa [prefixWord, tailWord_8153685, baseEnd_8153685] using wordTrace_append hprefix tailTrace_8153685
  have hstable : (prefixWord ++ tailWord_8153685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8153685).length < 2 ^ (prefixWord ++ tailWord_8153685).sum := by decide
  have hdescent : baseEnd_8153685 < baseStart_8153685 := by decide
  rcases family_descends (prefixWord ++ tailWord_8153685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8153699 : List Nat := [1, 1, 1, 5, 1, 2, 5, 1, 2, 4]
def baseStart_8153699 : Nat := 118140960795 + 8153699 * 2 ^ 59
def prefixEnd_8153699 : Nat := 4983230072969 + 3 ^ 40 * 8153699 * 2
def baseEnd_8153699 : Nat := 1395588899694733116288109

theorem tailTrace_8153699 : CollatzResearch.WordTrace tailWord_8153699 prefixEnd_8153699 1395588899694733116288109 := by
  unfold tailWord_8153699
  simp only [CollatzResearch.WordTrace]
  refine ⟨297389834087548538768464151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198259889391699025845642767 297389834087548538768464151)
  ·
    refine ⟨446084751131322808152696227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297389834087548538768464151 446084751131322808152696227)
    ·
      refine ⟨669127126696984212229044341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446084751131322808152696227 669127126696984212229044341)
      ·
        refine ⟨62730668127842269896472907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 669127126696984212229044341 62730668127842269896472907)
        ·
          refine ⟨94096002191763404844709361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62730668127842269896472907 94096002191763404844709361)
          ·
            refine ⟨70572001643822553633532021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94096002191763404844709361 70572001643822553633532021)
            ·
              refine ⟨6616125154108364403143627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70572001643822553633532021 6616125154108364403143627)
              ·
                refine ⟨9924187731162546604715441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6616125154108364403143627 9924187731162546604715441)
                ·
                  refine ⟨7443140798371909953536581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9924187731162546604715441 7443140798371909953536581)
                  ·
                    refine ⟨1395588899694733116288109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7443140798371909953536581 1395588899694733116288109)
                    ·
                      rfl

theorem cell23_8153699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 1, 2, 4].length) (baseStart_8153699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8153699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8153699 prefixEnd_8153699 := by exact prefixLift 8153699
  have htrace : WordTrace (prefixWord ++ tailWord_8153699) baseStart_8153699 baseEnd_8153699 := by
    simpa [prefixWord, tailWord_8153699, baseEnd_8153699] using wordTrace_append hprefix tailTrace_8153699
  have hstable : (prefixWord ++ tailWord_8153699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8153699).length < 2 ^ (prefixWord ++ tailWord_8153699).sum := by decide
  have hdescent : baseEnd_8153699 < baseStart_8153699 := by decide
  rcases family_descends (prefixWord ++ tailWord_8153699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8153709 : List Nat := [1, 5, 1, 1, 3, 1, 1, 4, 1, 2, 3]
def baseStart_8153709 : Nat := 118140960795 + 8153709 * 2 ^ 59
def prefixEnd_8153709 : Nat := 4983230072969 + 3 ^ 40 * 8153709 * 2
def baseEnd_8153709 : Nat := 4186771833890744309739281

theorem tailTrace_8153709 : CollatzResearch.WordTrace tailWord_8153709 prefixEnd_8153709 4186771833890744309739281 := by
  unfold tailWord_8153709
  simp only [CollatzResearch.WordTrace]
  refine ⟨297390198817512310476328181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198260132545008206984218787 297390198817512310476328181)
  ·
    refine ⟨27880331139141779107155767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 297390198817512310476328181 27880331139141779107155767)
    ·
      refine ⟨41820496708712668660733651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27880331139141779107155767 41820496708712668660733651)
      ·
        refine ⟨62730745063069002991100477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41820496708712668660733651 62730745063069002991100477)
        ·
          refine ⟨23524029398650876121662679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62730745063069002991100477 23524029398650876121662679)
          ·
            refine ⟨35286044097976314182494019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23524029398650876121662679 35286044097976314182494019)
            ·
              refine ⟨52929066146964471273741029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35286044097976314182494019 52929066146964471273741029)
              ·
                refine ⟨9924199902555838363826443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52929066146964471273741029 9924199902555838363826443)
                ·
                  refine ⟨14886299853833757545739665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9924199902555838363826443 14886299853833757545739665)
                  ·
                    refine ⟨11164724890375318159304749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14886299853833757545739665 11164724890375318159304749)
                    ·
                      refine ⟨4186771833890744309739281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11164724890375318159304749 4186771833890744309739281)
                      ·
                        rfl

theorem cell23_8153709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_8153709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8153709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8153709 prefixEnd_8153709 := by exact prefixLift 8153709
  have htrace : WordTrace (prefixWord ++ tailWord_8153709) baseStart_8153709 baseEnd_8153709 := by
    simpa [prefixWord, tailWord_8153709, baseEnd_8153709] using wordTrace_append hprefix tailTrace_8153709
  have hstable : (prefixWord ++ tailWord_8153709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8153709).length < 2 ^ (prefixWord ++ tailWord_8153709).sum := by decide
  have hdescent : baseEnd_8153709 < baseStart_8153709 := by decide
  rcases family_descends (prefixWord ++ tailWord_8153709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8153735 : List Nat := [1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 5]
def baseStart_8153735 : Nat := 118140960795 + 8153735 * 2 ^ 59
def prefixEnd_8153735 : Nat := 4983230072969 + 3 ^ 40 * 8153735 * 2
def baseEnd_8153735 : Nat := 4186785184387761208014161

theorem tailTrace_8153735 : CollatzResearch.WordTrace tailWord_8153735 prefixEnd_8153735 4186785184387761208014161 := by
  unfold tailWord_8153735
  simp only [CollatzResearch.WordTrace]
  refine ⟨297391147115418116916774659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198260764743612077944516439 297391147115418116916774659)
  ·
    refine ⟨446086720673127175375161989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297391147115418116916774659 446086720673127175375161989)
    ·
      refine ⟨83641260126211345382842873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 446086720673127175375161989 83641260126211345382842873)
      ·
        refine ⟨62730945094658509037132155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83641260126211345382842873 62730945094658509037132155)
        ·
          refine ⟨94096417641987763555698233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62730945094658509037132155 94096417641987763555698233)
          ·
            refine ⟨70572313231490822666773675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94096417641987763555698233 70572313231490822666773675)
            ·
              refine ⟨105858469847236234000160513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70572313231490822666773675 105858469847236234000160513)
              ·
                refine ⟨79393852385427175500120385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105858469847236234000160513 79393852385427175500120385)
                ·
                  refine ⟨59545389289070381625090289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79393852385427175500120385 59545389289070381625090289)
                  ·
                    refine ⟨44659041966802786218817717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59545389289070381625090289 44659041966802786218817717)
                    ·
                      refine ⟨4186785184387761208014161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44659041966802786218817717 4186785184387761208014161)
                      ·
                        rfl

theorem cell23_8153735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_8153735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8153735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8153735 prefixEnd_8153735 := by exact prefixLift 8153735
  have htrace : WordTrace (prefixWord ++ tailWord_8153735) baseStart_8153735 baseEnd_8153735 := by
    simpa [prefixWord, tailWord_8153735, baseEnd_8153735] using wordTrace_append hprefix tailTrace_8153735
  have hstable : (prefixWord ++ tailWord_8153735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8153735).length < 2 ^ (prefixWord ++ tailWord_8153735).sum := by decide
  have hdescent : baseEnd_8153735 < baseStart_8153735 := by decide
  rcases family_descends (prefixWord ++ tailWord_8153735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8153756 : List Nat := [2, 2, 3, 2, 2, 2, 1, 3, 2, 1, 3]
def baseStart_8153756 : Nat := 118140960795 + 8153756 * 2 ^ 59
def prefixEnd_8153756 : Nat := 4983230072969 + 3 ^ 40 * 8153756 * 2
def baseEnd_8153756 : Nat := 4186795967481505625851565

theorem tailTrace_8153756 : CollatzResearch.WordTrace tailWord_8153756 prefixEnd_8153756 4186795967481505625851565 := by
  unfold tailWord_8153756
  simp only [CollatzResearch.WordTrace]
  refine ⟨148695956524171018751644561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198261275365561358335526081 148695956524171018751644561)
  ·
    refine ⟨111521967393128264063733421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148695956524171018751644561 111521967393128264063733421)
    ·
      refine ⟨41820737772423099023900033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111521967393128264063733421 41820737772423099023900033)
      ·
        refine ⟨31365553329317324267925025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41820737772423099023900033 31365553329317324267925025)
        ·
          refine ⟨23524164996987993200943769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31365553329317324267925025 23524164996987993200943769)
          ·
            refine ⟨17643123747740994900707827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23524164996987993200943769 17643123747740994900707827)
            ·
              refine ⟨26464685621611492351061741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17643123747740994900707827 26464685621611492351061741)
              ·
                refine ⟨9924257108104309631648153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26464685621611492351061741 9924257108104309631648153)
                ·
                  refine ⟨7443192831078232223736115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9924257108104309631648153 7443192831078232223736115)
                  ·
                    refine ⟨11164789246617348335604173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7443192831078232223736115 11164789246617348335604173)
                    ·
                      refine ⟨4186795967481505625851565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11164789246617348335604173 4186795967481505625851565)
                      ·
                        rfl

theorem cell23_8153756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_8153756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8153756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8153756 prefixEnd_8153756 := by exact prefixLift 8153756
  have htrace : WordTrace (prefixWord ++ tailWord_8153756) baseStart_8153756 baseEnd_8153756 := by
    simpa [prefixWord, tailWord_8153756, baseEnd_8153756] using wordTrace_append hprefix tailTrace_8153756
  have hstable : (prefixWord ++ tailWord_8153756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8153756).length < 2 ^ (prefixWord ++ tailWord_8153756).sum := by decide
  have hdescent : baseEnd_8153756 < baseStart_8153756 := by decide
  rcases family_descends (prefixWord ++ tailWord_8153756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8153779 : List Nat := [1, 1, 1, 2, 3, 5, 1, 2, 1, 4, 2]
def baseStart_8153779 : Nat := 118140960795 + 8153779 * 2 ^ 59
def prefixEnd_8153779 : Nat := 4983230072969 + 3 ^ 40 * 8153779 * 2
def baseEnd_8153779 : Nat := 4186807777536559035863959

theorem tailTrace_8153779 : CollatzResearch.WordTrace tailWord_8153779 prefixEnd_8153779 4186807777536559035863959 := by
  unfold tailWord_8153779
  simp only [CollatzResearch.WordTrace]
  refine ⟨297392751927258712431376391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198261834618172474954250927 297392751927258712431376391)
  ·
    refine ⟨446089127890888068647064587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297392751927258712431376391 446089127890888068647064587)
    ·
      refine ⟨669133691836332102970596881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446089127890888068647064587 669133691836332102970596881)
      ·
        refine ⟨501850268877249077227947661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 669133691836332102970596881 501850268877249077227947661)
        ·
          refine ⟨188193850828968403960480373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 501850268877249077227947661 188193850828968403960480373)
          ·
            refine ⟨17643173515215787871295035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 188193850828968403960480373 17643173515215787871295035)
            ·
              refine ⟨26464760272823681806942553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17643173515215787871295035 26464760272823681806942553)
              ·
                refine ⟨19848570204617761355206915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26464760272823681806942553 19848570204617761355206915)
                ·
                  refine ⟨29772855306926642032810373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19848570204617761355206915 29772855306926642032810373)
                  ·
                    refine ⟨5582410370048745381151945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29772855306926642032810373 5582410370048745381151945)
                    ·
                      refine ⟨4186807777536559035863959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5582410370048745381151945 4186807777536559035863959)
                      ·
                        rfl

theorem cell23_8153779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 4, 2].length) (baseStart_8153779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8153779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8153779 prefixEnd_8153779 := by exact prefixLift 8153779
  have htrace : WordTrace (prefixWord ++ tailWord_8153779) baseStart_8153779 baseEnd_8153779 := by
    simpa [prefixWord, tailWord_8153779, baseEnd_8153779] using wordTrace_append hprefix tailTrace_8153779
  have hstable : (prefixWord ++ tailWord_8153779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8153779).length < 2 ^ (prefixWord ++ tailWord_8153779).sum := by decide
  have hdescent : baseEnd_8153779 < baseStart_8153779 := by decide
  rcases family_descends (prefixWord ++ tailWord_8153779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8153783 : List Nat := [1, 1, 3, 1, 6, 1, 3, 1, 1, 3, 2]
def baseStart_8153783 : Nat := 118140960795 + 8153783 * 2 ^ 59
def prefixEnd_8153783 : Nat := 4983230072969 + 3 ^ 40 * 8153783 * 2
def baseEnd_8153783 : Nat := 4186809831459177020213941

theorem tailTrace_8153783 : CollatzResearch.WordTrace tailWord_8153783 prefixEnd_8153783 4186809831459177020213941 := by
  unfold tailWord_8153783
  simp only [CollatzResearch.WordTrace]
  refine ⟨297392897819244221114522003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198261931879496147409681335 297392897819244221114522003)
  ·
    refine ⟨446089346728866331671783005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297392897819244221114522003 446089346728866331671783005)
    ·
      refine ⟨167283505023324874376918627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 446089346728866331671783005 167283505023324874376918627)
      ·
        refine ⟨250925257534987311565377941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167283505023324874376918627 250925257534987311565377941)
        ·
          refine ⟨11762121446952530229627091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 250925257534987311565377941 11762121446952530229627091)
          ·
            refine ⟨17643182170428795344440637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11762121446952530229627091 17643182170428795344440637)
            ·
              refine ⟨6616193313910798254165239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17643182170428795344440637 6616193313910798254165239)
              ·
                refine ⟨9924289970866197381247859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6616193313910798254165239 9924289970866197381247859)
                ·
                  refine ⟨14886434956299296071871789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9924289970866197381247859 14886434956299296071871789)
                  ·
                    refine ⟨5582413108612236026951921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14886434956299296071871789 5582413108612236026951921)
                    ·
                      refine ⟨4186809831459177020213941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5582413108612236026951921 4186809831459177020213941)
                      ·
                        rfl

theorem cell23_8153783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 1, 1, 3, 2].length) (baseStart_8153783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8153783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8153783 prefixEnd_8153783 := by exact prefixLift 8153783
  have htrace : WordTrace (prefixWord ++ tailWord_8153783) baseStart_8153783 baseEnd_8153783 := by
    simpa [prefixWord, tailWord_8153783, baseEnd_8153783] using wordTrace_append hprefix tailTrace_8153783
  have hstable : (prefixWord ++ tailWord_8153783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8153783).length < 2 ^ (prefixWord ++ tailWord_8153783).sum := by decide
  have hdescent : baseEnd_8153783 < baseStart_8153783 := by decide
  rcases family_descends (prefixWord ++ tailWord_8153783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8153813 : List Nat := [1, 3, 2, 5, 1, 1, 2, 1, 1, 4, 2]
def baseStart_8153813 : Nat := 118140960795 + 8153813 * 2 ^ 59
def prefixEnd_8153813 : Nat := 4983230072969 + 3 ^ 40 * 8153813 * 2
def baseEnd_8153813 : Nat := 4186825235878811902838803

theorem tailTrace_8153813 : CollatzResearch.WordTrace tailWord_8153813 prefixEnd_8153813 4186825235878811902838803 := by
  unfold tailWord_8153813
  simp only [CollatzResearch.WordTrace]
  refine ⟨297393992009135536238114093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198262661339423690825409395 297393992009135536238114093)
  ·
    refine ⟨111522747003425826089292785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297393992009135536238114093 111522747003425826089292785)
    ·
      refine ⟨83642060252569369566969589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111522747003425826089292785 83642060252569369566969589)
      ·
        refine ⟨7841443148678378396903399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83642060252569369566969589 7841443148678378396903399)
        ·
          refine ⟨11762164723017567595355099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7841443148678378396903399 11762164723017567595355099)
          ·
            refine ⟨17643247084526351393032649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11762164723017567595355099 17643247084526351393032649)
            ·
              refine ⟨13232435313394763544774487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17643247084526351393032649 13232435313394763544774487)
              ·
                refine ⟨19848652970092145317161731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13232435313394763544774487 19848652970092145317161731)
                ·
                  refine ⟨29772979455138217975742597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19848652970092145317161731 29772979455138217975742597)
                  ·
                    refine ⟨5582433647838415870451737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29772979455138217975742597 5582433647838415870451737)
                    ·
                      refine ⟨4186825235878811902838803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5582433647838415870451737 4186825235878811902838803)
                      ·
                        rfl

theorem cell23_8153813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_8153813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8153813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8153813 prefixEnd_8153813 := by exact prefixLift 8153813
  have htrace : WordTrace (prefixWord ++ tailWord_8153813) baseStart_8153813 baseEnd_8153813 := by
    simpa [prefixWord, tailWord_8153813, baseEnd_8153813] using wordTrace_append hprefix tailTrace_8153813
  have hstable : (prefixWord ++ tailWord_8153813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8153813).length < 2 ^ (prefixWord ++ tailWord_8153813).sum := by decide
  have hdescent : baseEnd_8153813 < baseStart_8153813 := by decide
  rcases family_descends (prefixWord ++ tailWord_8153813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8153882 : List Nat := [3, 1, 1, 3, 2, 1, 1, 1, 2, 4, 4]
def baseStart_8153882 : Nat := 118140960795 + 8153882 * 2 ^ 59
def prefixEnd_8153882 : Nat := 4983230072969 + 3 ^ 40 * 8153882 * 2
def baseEnd_8153882 : Nat := 4186860666043972132875985

theorem tailTrace_8153882 : CollatzResearch.WordTrace tailWord_8153882 prefixEnd_8153882 4186860666043972132875985 := by
  unfold tailWord_8153882
  simp only [CollatzResearch.WordTrace]
  refine ⟨74349127161471390255593975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198264339097257040681583933 74349127161471390255593975)
  ·
    refine ⟨111523690742207085383390963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74349127161471390255593975 111523690742207085383390963)
    ·
      refine ⟨167285536113310628075086445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111523690742207085383390963 167285536113310628075086445)
      ·
        refine ⟨62732076042491485528157417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167285536113310628075086445 62732076042491485528157417)
        ·
          refine ⟨47049057031868614146118063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62732076042491485528157417 47049057031868614146118063)
          ·
            refine ⟨70573585547802921219177095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47049057031868614146118063 70573585547802921219177095)
            ·
              refine ⟨105860378321704381828765643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70573585547802921219177095 105860378321704381828765643)
              ·
                refine ⟨158790567482556572743148465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105860378321704381828765643 158790567482556572743148465)
                ·
                  refine ⟨119092925611917429557361349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158790567482556572743148465 119092925611917429557361349)
                  ·
                    refine ⟨22329923552234518042005253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 119092925611917429557361349 22329923552234518042005253)
                    ·
                      refine ⟨4186860666043972132875985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22329923552234518042005253 4186860666043972132875985)
                      ·
                        rfl

theorem cell23_8153882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_8153882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8153882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8153882 prefixEnd_8153882 := by exact prefixLift 8153882
  have htrace : WordTrace (prefixWord ++ tailWord_8153882) baseStart_8153882 baseEnd_8153882 := by
    simpa [prefixWord, tailWord_8153882, baseEnd_8153882] using wordTrace_append hprefix tailTrace_8153882
  have hstable : (prefixWord ++ tailWord_8153882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8153882).length < 2 ^ (prefixWord ++ tailWord_8153882).sum := by decide
  have hdescent : baseEnd_8153882 < baseStart_8153882 := by decide
  rcases family_descends (prefixWord ++ tailWord_8153882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8153889 : List Nat := [1, 2, 3, 2, 1, 2, 2, 3, 2, 2, 3]
def baseStart_8153889 : Nat := 118140960795 + 8153889 * 2 ^ 59
def prefixEnd_8153889 : Nat := 4983230072969 + 3 ^ 40 * 8153889 * 2
def baseEnd_8153889 : Nat := 4186864260408553605488453

theorem tailTrace_8153889 : CollatzResearch.WordTrace tailWord_8153889 prefixEnd_8153889 4186864260408553605488453 := by
  unfold tailWord_8153889
  simp only [CollatzResearch.WordTrace]
  refine ⟨297396763956860201217880721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198264509304573467478587147 297396763956860201217880721)
  ·
    refine ⟨223047572967645150913410541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297396763956860201217880721 223047572967645150913410541)
    ·
      refine ⟨83642839862866931592528953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223047572967645150913410541 83642839862866931592528953)
      ·
        refine ⟨62732129897150198694396715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83642839862866931592528953 62732129897150198694396715)
        ·
          refine ⟨94098194845725298041595073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62732129897150198694396715 94098194845725298041595073)
          ·
            refine ⟨70573646134293973531196305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94098194845725298041595073 70573646134293973531196305)
            ·
              refine ⟨52930234600720480148397229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70573646134293973531196305 52930234600720480148397229)
              ·
                refine ⟨19848837975270180055648961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52930234600720480148397229 19848837975270180055648961)
                ·
                  refine ⟨14886628481452635041736721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19848837975270180055648961 14886628481452635041736721)
                  ·
                    refine ⟨11164971361089476281302541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14886628481452635041736721 11164971361089476281302541)
                    ·
                      refine ⟨4186864260408553605488453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11164971361089476281302541 4186864260408553605488453)
                      ·
                        rfl

theorem cell23_8153889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_8153889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8153889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8153889 prefixEnd_8153889 := by exact prefixLift 8153889
  have htrace : WordTrace (prefixWord ++ tailWord_8153889) baseStart_8153889 baseEnd_8153889 := by
    simpa [prefixWord, tailWord_8153889, baseEnd_8153889] using wordTrace_append hprefix tailTrace_8153889
  have hstable : (prefixWord ++ tailWord_8153889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8153889).length < 2 ^ (prefixWord ++ tailWord_8153889).sum := by decide
  have hdescent : baseEnd_8153889 < baseStart_8153889 := by decide
  rcases family_descends (prefixWord ++ tailWord_8153889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8153946 : List Nat := [3, 1, 1, 2, 1, 4, 1, 3, 2, 3, 2]
def baseStart_8153946 : Nat := 118140960795 + 8153946 * 2 ^ 59
def prefixEnd_8153946 : Nat := 4983230072969 + 3 ^ 40 * 8153946 * 2
def baseEnd_8153946 : Nat := 4186893528805859882475691

theorem tailTrace_8153946 : CollatzResearch.WordTrace tailWord_8153946 prefixEnd_8153946 4186893528805859882475691 := by
  unfold tailWord_8153946
  simp only [CollatzResearch.WordTrace]
  refine ⟨74349710729413424988176423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198265895278435799968470461 74349710729413424988176423)
  ·
    refine ⟨111524566094120137482264635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74349710729413424988176423 111524566094120137482264635)
    ·
      refine ⟨167286849141180206223396953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111524566094120137482264635 167286849141180206223396953)
      ·
        refine ⟨125465136855885154667547715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167286849141180206223396953 125465136855885154667547715)
        ·
          refine ⟨188197705283827732001321573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125465136855885154667547715 188197705283827732001321573)
          ·
            refine ⟨35287069740717699750247795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188197705283827732001321573 35287069740717699750247795)
            ·
              refine ⟨52930604611076549625371693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35287069740717699750247795 52930604611076549625371693)
              ·
                refine ⟨19848976729153706109514385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52930604611076549625371693 19848976729153706109514385)
                ·
                  refine ⟨14886732546865279582135789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19848976729153706109514385 14886732546865279582135789)
                  ·
                    refine ⟨5582524705074479843300921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14886732546865279582135789 5582524705074479843300921)
                    ·
                      refine ⟨4186893528805859882475691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5582524705074479843300921 4186893528805859882475691)
                      ·
                        rfl

theorem cell23_8153946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 2, 3, 2].length) (baseStart_8153946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8153946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8153946 prefixEnd_8153946 := by exact prefixLift 8153946
  have htrace : WordTrace (prefixWord ++ tailWord_8153946) baseStart_8153946 baseEnd_8153946 := by
    simpa [prefixWord, tailWord_8153946, baseEnd_8153946] using wordTrace_append hprefix tailTrace_8153946
  have hstable : (prefixWord ++ tailWord_8153946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8153946).length < 2 ^ (prefixWord ++ tailWord_8153946).sum := by decide
  have hdescent : baseEnd_8153946 < baseStart_8153946 := by decide
  rcases family_descends (prefixWord ++ tailWord_8153946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8153970 : List Nat := [3, 2, 1, 2, 1, 1, 6, 2, 1, 1, 3]
def baseStart_8153970 : Nat := 118140960795 + 8153970 * 2 ^ 59
def prefixEnd_8153970 : Nat := 4983230072969 + 3 ^ 40 * 8153970 * 2
def baseEnd_8153970 : Nat := 4186905852341567788575581

theorem tailTrace_8153970 : CollatzResearch.WordTrace tailWord_8153970 prefixEnd_8153970 4186905852341567788575581 := by
  unfold tailWord_8153970
  simp only [CollatzResearch.WordTrace]
  refine ⟨74349929567391688012894841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198266478846377834701052909 74349929567391688012894841)
  ·
    refine ⟨55762447175543766009671131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74349929567391688012894841 55762447175543766009671131)
    ·
      refine ⟨83643670763315649014506697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55762447175543766009671131 83643670763315649014506697)
      ·
        refine ⟨62732753072486736760880023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83643670763315649014506697 62732753072486736760880023)
        ·
          refine ⟨94099129608730105141320035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62732753072486736760880023 94099129608730105141320035)
          ·
            refine ⟨141148694413095157711980053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94099129608730105141320035 141148694413095157711980053)
            ·
              refine ⟨6616345050613835517749065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 141148694413095157711980053 6616345050613835517749065)
              ·
                refine ⟨4962258787960376638311799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6616345050613835517749065 4962258787960376638311799)
                ·
                  refine ⟨7443388181940564957467699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4962258787960376638311799 7443388181940564957467699)
                  ·
                    refine ⟨11165082272910847436201549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7443388181940564957467699 11165082272910847436201549)
                    ·
                      refine ⟨4186905852341567788575581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11165082272910847436201549 4186905852341567788575581)
                      ·
                        rfl

theorem cell23_8153970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 2, 1, 1, 3].length) (baseStart_8153970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8153970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8153970 prefixEnd_8153970 := by exact prefixLift 8153970
  have htrace : WordTrace (prefixWord ++ tailWord_8153970) baseStart_8153970 baseEnd_8153970 := by
    simpa [prefixWord, tailWord_8153970, baseEnd_8153970] using wordTrace_append hprefix tailTrace_8153970
  have hstable : (prefixWord ++ tailWord_8153970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8153970).length < 2 ^ (prefixWord ++ tailWord_8153970).sum := by decide
  have hdescent : baseEnd_8153970 < baseStart_8153970 := by decide
  rcases family_descends (prefixWord ++ tailWord_8153970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8153979 : List Nat := [1, 1, 1, 1, 1, 5, 3, 2, 3, 2, 3]
def baseStart_8153979 : Nat := 118140960795 + 8153979 * 2 ^ 59
def prefixEnd_8153979 : Nat := 4983230072969 + 3 ^ 40 * 8153979 * 2
def baseEnd_8153979 : Nat := 4186910473667458253363039

theorem tailTrace_8153979 : CollatzResearch.WordTrace tailWord_8153979 prefixEnd_8153979 4186910473667458253363039 := by
  unfold tailWord_8153979
  simp only [CollatzResearch.WordTrace]
  refine ⟨297400046526534146588656991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198266697684356097725771327 297400046526534146588656991)
  ·
    refine ⟨446100069789801219882985487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297400046526534146588656991 446100069789801219882985487)
    ·
      refine ⟨669150104684701829824478231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446100069789801219882985487 669150104684701829824478231)
      ·
        refine ⟨1003725157027052744736717347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 669150104684701829824478231 1003725157027052744736717347)
        ·
          refine ⟨1505587735540579117105076021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1003725157027052744736717347 1505587735540579117105076021)
          ·
            refine ⟨141148850206929292228600877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1505587735540579117105076021 141148850206929292228600877)
            ·
              refine ⟨52930818827598484585725329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141148850206929292228600877 52930818827598484585725329)
              ·
                refine ⟨39698114120698863439293997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52930818827598484585725329 39698114120698863439293997)
                ·
                  refine ⟨14886792795262073789735249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39698114120698863439293997 14886792795262073789735249)
                  ·
                    refine ⟨11165094596446555342301437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14886792795262073789735249 11165094596446555342301437)
                    ·
                      refine ⟨4186910473667458253363039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11165094596446555342301437 4186910473667458253363039)
                      ·
                        rfl

theorem cell23_8153979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 3, 2, 3].length) (baseStart_8153979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8153979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8153979 prefixEnd_8153979 := by exact prefixLift 8153979
  have htrace : WordTrace (prefixWord ++ tailWord_8153979) baseStart_8153979 baseEnd_8153979 := by
    simpa [prefixWord, tailWord_8153979, baseEnd_8153979] using wordTrace_append hprefix tailTrace_8153979
  have hstable : (prefixWord ++ tailWord_8153979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8153979).length < 2 ^ (prefixWord ++ tailWord_8153979).sum := by decide
  have hdescent : baseEnd_8153979 < baseStart_8153979 := by decide
  rcases family_descends (prefixWord ++ tailWord_8153979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8153989 : List Nat := [1, 3, 1, 1, 3, 3, 1, 3, 1, 2, 4]
def baseStart_8153989 : Nat := 118140960795 + 8153989 * 2 ^ 59
def prefixEnd_8153989 : Nat := 4983230072969 + 3 ^ 40 * 8153989 * 2
def baseEnd_8153989 : Nat := 4186915608474003214237993

theorem tailTrace_8153989 : CollatzResearch.WordTrace tailWord_8153989 prefixEnd_8153989 4186915608474003214237993 := by
  unfold tailWord_8153989
  simp only [CollatzResearch.WordTrace]
  refine ⟨297400411256497918296521021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198266940837665278864347347 297400411256497918296521021)
  ·
    refine ⟨111525154221186719361195383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297400411256497918296521021 111525154221186719361195383)
    ·
      refine ⟨167287731331780079041793075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111525154221186719361195383 167287731331780079041793075)
      ·
        refine ⟨250931596997670118562689613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167287731331780079041793075 250931596997670118562689613)
        ·
          refine ⟨94099348874126294461008605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250931596997670118562689613 94099348874126294461008605)
          ·
            refine ⟨35287255827797360422878227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94099348874126294461008605 35287255827797360422878227)
            ·
              refine ⟨52930883741696040634317341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35287255827797360422878227 52930883741696040634317341)
              ·
                refine ⟨19849081403136015237869003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52930883741696040634317341 19849081403136015237869003)
                ·
                  refine ⟨29773622104704022856803505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19849081403136015237869003 29773622104704022856803505)
                  ·
                    refine ⟨22330216578528017142602629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29773622104704022856803505 22330216578528017142602629)
                    ·
                      refine ⟨4186915608474003214237993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22330216578528017142602629 4186915608474003214237993)
                      ·
                        rfl

theorem cell23_8153989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 2, 4].length) (baseStart_8153989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8153989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8153989 prefixEnd_8153989 := by exact prefixLift 8153989
  have htrace : WordTrace (prefixWord ++ tailWord_8153989) baseStart_8153989 baseEnd_8153989 := by
    simpa [prefixWord, tailWord_8153989, baseEnd_8153989] using wordTrace_append hprefix tailTrace_8153989
  have hstable : (prefixWord ++ tailWord_8153989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8153989).length < 2 ^ (prefixWord ++ tailWord_8153989).sum := by decide
  have hdescent : baseEnd_8153989 < baseStart_8153989 := by decide
  rcases family_descends (prefixWord ++ tailWord_8153989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8153993 : List Nat := [1, 2, 1, 1, 5, 3, 1, 2, 3, 2, 2]
def baseStart_8153993 : Nat := 118140960795 + 8153993 * 2 ^ 59
def prefixEnd_8153993 : Nat := 4983230072969 + 3 ^ 40 * 8153993 * 2
def baseEnd_8153993 : Nat := 4186917662396621198587975

theorem tailTrace_8153993 : CollatzResearch.WordTrace tailWord_8153993 prefixEnd_8153993 4186917662396621198587975 := by
  unfold tailWord_8153993
  simp only [CollatzResearch.WordTrace]
  refine ⟨297400557148483426979666633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198267038098988951319777755 297400557148483426979666633)
  ·
    refine ⟨223050417861362570234749975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297400557148483426979666633 223050417861362570234749975)
    ·
      refine ⟨334575626792043855352124963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223050417861362570234749975 334575626792043855352124963)
      ·
        refine ⟨501863440188065783028187445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334575626792043855352124963 501863440188065783028187445)
        ·
          refine ⟨47049697517631167158892573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 501863440188065783028187445 47049697517631167158892573)
          ·
            refine ⟨17643636569111687684584715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47049697517631167158892573 17643636569111687684584715)
            ·
              refine ⟨26465454853667531526877073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17643636569111687684584715 26465454853667531526877073)
              ·
                refine ⟨19849091140250648645157805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26465454853667531526877073 19849091140250648645157805)
                ·
                  refine ⟨7443409177593993241934177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19849091140250648645157805 7443409177593993241934177)
                  ·
                    refine ⟨5582556883195494931450633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7443409177593993241934177 5582556883195494931450633)
                    ·
                      refine ⟨4186917662396621198587975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5582556883195494931450633 4186917662396621198587975)
                      ·
                        rfl

theorem cell23_8153993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 3, 2, 2].length) (baseStart_8153993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8153993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8153993 prefixEnd_8153993 := by exact prefixLift 8153993
  have htrace : WordTrace (prefixWord ++ tailWord_8153993) baseStart_8153993 baseEnd_8153993 := by
    simpa [prefixWord, tailWord_8153993, baseEnd_8153993] using wordTrace_append hprefix tailTrace_8153993
  have hstable : (prefixWord ++ tailWord_8153993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8153993).length < 2 ^ (prefixWord ++ tailWord_8153993).sum := by decide
  have hdescent : baseEnd_8153993 < baseStart_8153993 := by decide
  rcases family_descends (prefixWord ++ tailWord_8153993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8154010 : List Nat := [3, 1, 1, 4, 3, 2, 2, 1, 1, 1, 4]
def baseStart_8154010 : Nat := 118140960795 + 8154010 * 2 ^ 59
def prefixEnd_8154010 : Nat := 4983230072969 + 3 ^ 40 * 8154010 * 2
def baseEnd_8154010 : Nat := 4186926391567747632075397

theorem tailTrace_8154010 : CollatzResearch.WordTrace tailWord_8154010 prefixEnd_8154010 4186926391567747632075397 := by
  unfold tailWord_8154010
  simp only [CollatzResearch.WordTrace]
  refine ⟨74350294297355459720758871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198267451459614559255356989 74350294297355459720758871)
  ·
    refine ⟨111525441446033189581138307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74350294297355459720758871 111525441446033189581138307)
    ·
      refine ⟨167288162169049784371707461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111525441446033189581138307 167288162169049784371707461)
      ·
        refine ⟨31366530406696834569695149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167288162169049784371707461 31366530406696834569695149)
        ·
          refine ⟨11762448902511312963635681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31366530406696834569695149 11762448902511312963635681)
          ·
            refine ⟨8821836676883484722726761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11762448902511312963635681 8821836676883484722726761)
            ·
              refine ⟨6616377507662613542045071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8821836676883484722726761 6616377507662613542045071)
              ·
                refine ⟨9924566261493920313067607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6616377507662613542045071 9924566261493920313067607)
                ·
                  refine ⟨14886849392240880469601411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9924566261493920313067607 14886849392240880469601411)
                  ·
                    refine ⟨22330274088361320704402117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14886849392240880469601411 22330274088361320704402117)
                    ·
                      refine ⟨4186926391567747632075397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22330274088361320704402117 4186926391567747632075397)
                      ·
                        rfl

theorem cell23_8154010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_8154010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8154010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8154010 prefixEnd_8154010 := by exact prefixLift 8154010
  have htrace : WordTrace (prefixWord ++ tailWord_8154010) baseStart_8154010 baseEnd_8154010 := by
    simpa [prefixWord, tailWord_8154010, baseEnd_8154010] using wordTrace_append hprefix tailTrace_8154010
  have hstable : (prefixWord ++ tailWord_8154010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8154010).length < 2 ^ (prefixWord ++ tailWord_8154010).sum := by decide
  have hdescent : baseEnd_8154010 < baseStart_8154010 := by decide
  rcases family_descends (prefixWord ++ tailWord_8154010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8154083 : List Nat := [1, 1, 1, 6, 1, 1, 1, 3, 4, 2, 2]
def baseStart_8154083 : Nat := 118140960795 + 8154083 * 2 ^ 59
def prefixEnd_8154083 : Nat := 4983230072969 + 3 ^ 40 * 8154083 * 2
def baseEnd_8154083 : Nat := 4186963875655525846462561

theorem tailTrace_8154083 : CollatzResearch.WordTrace tailWord_8154083 prefixEnd_8154083 4186963875655525846462561 := by
  unfold tailWord_8154083
  simp only [CollatzResearch.WordTrace]
  refine ⟨297403839718157372350442903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198269226478771581566961935 297403839718157372350442903)
  ·
    refine ⟨446105759577236058525664355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297403839718157372350442903 446105759577236058525664355)
    ·
      refine ⟨669158639365854087788496533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446105759577236058525664355 669158639365854087788496533)
      ·
        refine ⟨31366811220274410365085775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 669158639365854087788496533 31366811220274410365085775)
        ·
          refine ⟨47050216830411615547628663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31366811220274410365085775 47050216830411615547628663)
          ·
            refine ⟨70575325245617423321442995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47050216830411615547628663 70575325245617423321442995)
            ·
              refine ⟨105862987868426134982164493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70575325245617423321442995 105862987868426134982164493)
              ·
                refine ⟨39698620450659800618311685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105862987868426134982164493 39698620450659800618311685)
                ·
                  refine ⟨7443491334498712615933441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39698620450659800618311685 7443491334498712615933441)
                  ·
                    refine ⟨5582618500874034461950081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7443491334498712615933441 5582618500874034461950081)
                    ·
                      refine ⟨4186963875655525846462561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5582618500874034461950081 4186963875655525846462561)
                      ·
                        rfl

theorem cell23_8154083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_8154083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8154083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8154083 prefixEnd_8154083 := by exact prefixLift 8154083
  have htrace : WordTrace (prefixWord ++ tailWord_8154083) baseStart_8154083 baseEnd_8154083 := by
    simpa [prefixWord, tailWord_8154083, baseEnd_8154083] using wordTrace_append hprefix tailTrace_8154083
  have hstable : (prefixWord ++ tailWord_8154083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8154083).length < 2 ^ (prefixWord ++ tailWord_8154083).sum := by decide
  have hdescent : baseEnd_8154083 < baseStart_8154083 := by decide
  rcases family_descends (prefixWord ++ tailWord_8154083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8154094 : List Nat := [4, 1, 2, 1, 5, 1, 2, 1, 2, 1, 3]
def baseStart_8154094 : Nat := 118140960795 + 8154094 * 2 ^ 59
def prefixEnd_8154094 : Nat := 4983230072969 + 3 ^ 40 * 8154094 * 2
def baseEnd_8154094 : Nat := 4186969523942725303425011

theorem tailTrace_8154094 : CollatzResearch.WordTrace tailWord_8154094 prefixEnd_8154094 4186969523942725303425011 := by
  unfold tailWord_8154094
  simp only [CollatzResearch.WordTrace]
  refine ⟨37175530115139690153636667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198269493947411680819395557 37175530115139690153636667)
  ·
    refine ⟨55763295172709535230455001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37175530115139690153636667 55763295172709535230455001)
    ·
      refine ⟨41822471379532151422841251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55763295172709535230455001 41822471379532151422841251)
      ·
        refine ⟨62733707069298227134261877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41822471379532151422841251 62733707069298227134261877)
        ·
          refine ⟨5881285037746708793837051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62733707069298227134261877 5881285037746708793837051)
          ·
            refine ⟨8821927556620063190755577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5881285037746708793837051 8821927556620063190755577)
            ·
              refine ⟨6616445667465047393066683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8821927556620063190755577 6616445667465047393066683)
              ·
                refine ⟨9924668501197571089600025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6616445667465047393066683 9924668501197571089600025)
                ·
                  refine ⟨7443501375898178317200019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9924668501197571089600025 7443501375898178317200019)
                  ·
                    refine ⟨11165252063847267475800029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7443501375898178317200019 11165252063847267475800029)
                    ·
                      refine ⟨4186969523942725303425011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11165252063847267475800029 4186969523942725303425011)
                      ·
                        rfl

theorem cell23_8154094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 1, 2, 1, 3].length) (baseStart_8154094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8154094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8154094 prefixEnd_8154094 := by exact prefixLift 8154094
  have htrace : WordTrace (prefixWord ++ tailWord_8154094) baseStart_8154094 baseEnd_8154094 := by
    simpa [prefixWord, tailWord_8154094, baseEnd_8154094] using wordTrace_append hprefix tailTrace_8154094
  have hstable : (prefixWord ++ tailWord_8154094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8154094).length < 2 ^ (prefixWord ++ tailWord_8154094).sum := by decide
  have hdescent : baseEnd_8154094 < baseStart_8154094 := by decide
  rcases family_descends (prefixWord ++ tailWord_8154094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8154136 : List Nat := [2, 1, 2, 3, 2, 2, 2, 2, 2, 5]
def baseStart_8154136 : Nat := 118140960795 + 8154136 * 2 ^ 59
def prefixEnd_8154136 : Nat := 4983230072969 + 3 ^ 40 * 8154136 * 2
def baseEnd_8154136 : Nat := 1395663696710071379699939

theorem tailTrace_8154136 : CollatzResearch.WordTrace tailWord_8154136 prefixEnd_8154136 1395663696710071379699939 := by
  unfold tailWord_8154136
  simp only [CollatzResearch.WordTrace]
  refine ⟨148702886393482681201061131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198270515191310241601414841 148702886393482681201061131)
  ·
    refine ⟨223054329590224021801591697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148702886393482681201061131 223054329590224021801591697)
    ·
      refine ⟨167290747192668016351193773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223054329590224021801591697 167290747192668016351193773)
      ·
        refine ⟨62734030197250506131697665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167290747192668016351193773 62734030197250506131697665)
        ·
          refine ⟨47050522647937879598773249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62734030197250506131697665 47050522647937879598773249)
          ·
            refine ⟨35287891985953409699079937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47050522647937879598773249 35287891985953409699079937)
            ·
              refine ⟨26465918989465057274309953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35287891985953409699079937 26465918989465057274309953)
              ·
                refine ⟨19849439242098792955732465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26465918989465057274309953 19849439242098792955732465)
                ·
                  refine ⟨14887079431574094716799349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19849439242098792955732465 14887079431574094716799349)
                  ·
                    refine ⟨1395663696710071379699939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14887079431574094716799349 1395663696710071379699939)
                    ·
                      rfl

theorem cell23_8154136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 2, 5].length) (baseStart_8154136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8154136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8154136 prefixEnd_8154136 := by exact prefixLift 8154136
  have htrace : WordTrace (prefixWord ++ tailWord_8154136) baseStart_8154136 baseEnd_8154136 := by
    simpa [prefixWord, tailWord_8154136, baseEnd_8154136] using wordTrace_append hprefix tailTrace_8154136
  have hstable : (prefixWord ++ tailWord_8154136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8154136).length < 2 ^ (prefixWord ++ tailWord_8154136).sum := by decide
  have hdescent : baseEnd_8154136 < baseStart_8154136 := by decide
  rcases family_descends (prefixWord ++ tailWord_8154136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8154146 : List Nat := [3, 3, 1, 1, 1, 3, 2, 1, 1, 2, 5]
def baseStart_8154146 : Nat := 118140960795 + 8154146 * 2 ^ 59
def prefixEnd_8154146 : Nat := 4983230072969 + 3 ^ 40 * 8154146 * 2
def baseEnd_8154146 : Nat := 4186996224936759099974771

theorem tailTrace_8154146 : CollatzResearch.WordTrace tailWord_8154146 prefixEnd_8154146 4186996224936759099974771 := by
  unfold tailWord_8154146
  simp only [CollatzResearch.WordTrace]
  refine ⟨74351534379232283527496573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198270758344619422739990861 74351534379232283527496573)
  ·
    refine ⟨27881825392212106322811215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74351534379232283527496573 27881825392212106322811215)
    ·
      refine ⟨41822738088318159484216823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27881825392212106322811215 41822738088318159484216823)
      ·
        refine ⟨62734107132477239226325235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41822738088318159484216823 62734107132477239226325235)
        ·
          refine ⟨94101160698715858839487853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62734107132477239226325235 94101160698715858839487853)
          ·
            refine ⟨35287935262018447064807945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94101160698715858839487853 35287935262018447064807945)
            ·
              refine ⟨26465951446513835298605959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35287935262018447064807945 26465951446513835298605959)
              ·
                refine ⟨39698927169770752947908939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26465951446513835298605959 39698927169770752947908939)
                ·
                  refine ⟨59548390754656129421863409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39698927169770752947908939 59548390754656129421863409)
                  ·
                    refine ⟨44661293065992097066397557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59548390754656129421863409 44661293065992097066397557)
                    ·
                      refine ⟨4186996224936759099974771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44661293065992097066397557 4186996224936759099974771)
                      ·
                        rfl

theorem cell23_8154146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_8154146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8154146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8154146 prefixEnd_8154146 := by exact prefixLift 8154146
  have htrace : WordTrace (prefixWord ++ tailWord_8154146) baseStart_8154146 baseEnd_8154146 := by
    simpa [prefixWord, tailWord_8154146, baseEnd_8154146] using wordTrace_append hprefix tailTrace_8154146
  have hstable : (prefixWord ++ tailWord_8154146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8154146).length < 2 ^ (prefixWord ++ tailWord_8154146).sum := by decide
  have hdescent : baseEnd_8154146 < baseStart_8154146 := by decide
  rcases family_descends (prefixWord ++ tailWord_8154146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8154173 : List Nat := [1, 4, 1, 3, 1, 2, 3, 1, 2, 1, 4]
def baseStart_8154173 : Nat := 118140960795 + 8154173 * 2 ^ 59
def prefixEnd_8154173 : Nat := 4983230072969 + 3 ^ 40 * 8154173 * 2
def baseEnd_8154173 : Nat := 4187010088914430494337147

theorem tailTrace_8154173 : CollatzResearch.WordTrace tailWord_8154173 prefixEnd_8154173 4187010088914430494337147 := by
  unfold tailWord_8154173
  simp only [CollatzResearch.WordTrace]
  refine ⟨297407122287831317721219173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198271414858554211814146115 297407122287831317721219173)
  ·
    refine ⟨55763835428968372072728595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 297407122287831317721219173 55763835428968372072728595)
    ·
      refine ⟨83645753143452558109092893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55763835428968372072728595 83645753143452558109092893)
      ·
        refine ⟨31367157428794709290909835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83645753143452558109092893 31367157428794709290909835)
        ·
          refine ⟨47050736143192063936364753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31367157428794709290909835 47050736143192063936364753)
          ·
            refine ⟨35288052107394047952273565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47050736143192063936364753 35288052107394047952273565)
            ·
              refine ⟨13233019540272767982102587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35288052107394047952273565 13233019540272767982102587)
              ·
                refine ⟨19849529310409151973153881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13233019540272767982102587 19849529310409151973153881)
                ·
                  refine ⟨14887146982806863979865411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19849529310409151973153881 14887146982806863979865411)
                  ·
                    refine ⟨22330720474210295969798117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14887146982806863979865411 22330720474210295969798117)
                    ·
                      refine ⟨4187010088914430494337147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22330720474210295969798117 4187010088914430494337147)
                      ·
                        rfl

theorem cell23_8154173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_8154173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8154173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8154173 prefixEnd_8154173 := by exact prefixLift 8154173
  have htrace : WordTrace (prefixWord ++ tailWord_8154173) baseStart_8154173 baseEnd_8154173 := by
    simpa [prefixWord, tailWord_8154173, baseEnd_8154173] using wordTrace_append hprefix tailTrace_8154173
  have hstable : (prefixWord ++ tailWord_8154173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8154173).length < 2 ^ (prefixWord ++ tailWord_8154173).sum := by decide
  have hdescent : baseEnd_8154173 < baseStart_8154173 := by decide
  rcases family_descends (prefixWord ++ tailWord_8154173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8154176 : List Nat := [2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 3]
def baseStart_8154176 : Nat := 118140960795 + 8154176 * 2 ^ 59
def prefixEnd_8154176 : Nat := 4983230072969 + 3 ^ 40 * 8154176 * 2
def baseEnd_8154176 : Nat := 4187011629356393982599633

theorem tailTrace_8154176 : CollatzResearch.WordTrace tailWord_8154176 prefixEnd_8154176 4187011629356393982599633 := by
  unfold tailWord_8154176
  simp only [CollatzResearch.WordTrace]
  refine ⟨148703615853410224616789191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198271487804546966155718921 148703615853410224616789191)
  ·
    refine ⟨223055423780115336925183787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148703615853410224616789191 223055423780115336925183787)
    ·
      refine ⟨334583135670173005387775681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223055423780115336925183787 334583135670173005387775681)
      ·
        refine ⟨250937351752629754040831761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334583135670173005387775681 250937351752629754040831761)
        ·
          refine ⟨188203013814472315530623821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250937351752629754040831761 188203013814472315530623821)
          ·
            refine ⟨70576130180427118323983933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188203013814472315530623821 70576130180427118323983933)
            ·
              refine ⟨26466048817660169371493975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70576130180427118323983933 26466048817660169371493975)
              ·
                refine ⟨39699073226490254057240963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26466048817660169371493975 39699073226490254057240963)
                ·
                  refine ⟨59548609839735381085861445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39699073226490254057240963 59548609839735381085861445)
                  ·
                    refine ⟨11165364344950383953599021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59548609839735381085861445 11165364344950383953599021)
                    ·
                      refine ⟨4187011629356393982599633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11165364344950383953599021 4187011629356393982599633)
                      ·
                        rfl

theorem cell23_8154176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 3].length) (baseStart_8154176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8154176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8154176 prefixEnd_8154176 := by exact prefixLift 8154176
  have htrace : WordTrace (prefixWord ++ tailWord_8154176) baseStart_8154176 baseEnd_8154176 := by
    simpa [prefixWord, tailWord_8154176, baseEnd_8154176] using wordTrace_append hprefix tailTrace_8154176
  have hstable : (prefixWord ++ tailWord_8154176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8154176).length < 2 ^ (prefixWord ++ tailWord_8154176).sum := by decide
  have hdescent : baseEnd_8154176 < baseStart_8154176 := by decide
  rcases family_descends (prefixWord ++ tailWord_8154176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8154179 : List Nat := [1, 1, 1, 3, 1, 2, 4, 2, 8]
def baseStart_8154179 : Nat := 118140960795 + 8154179 * 2 ^ 59
def prefixEnd_8154179 : Nat := 4983230072969 + 3 ^ 40 * 8154179 * 2
def baseEnd_8154179 : Nat := 465223685533150830095791

theorem tailTrace_8154179 : CollatzResearch.WordTrace tailWord_8154179 prefixEnd_8154179 465223685533150830095791 := by
  unfold tailWord_8154179
  simp only [CollatzResearch.WordTrace]
  refine ⟨297407341125809580745937591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198271560750539720497291727 297407341125809580745937591)
  ·
    refine ⟨446111011688714371118906387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297407341125809580745937591 446111011688714371118906387)
    ·
      refine ⟨669166517533071556678359581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446111011688714371118906387 669166517533071556678359581)
      ·
        refine ⟨250937444074901833754384843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 669166517533071556678359581 250937444074901833754384843)
        ·
          refine ⟨376406166112352750631577265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250937444074901833754384843 376406166112352750631577265)
          ·
            refine ⟨282304624584264562973682949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 376406166112352750631577265 282304624584264562973682949)
            ·
              refine ⟨52932117109549605557565553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 282304624584264562973682949 52932117109549605557565553)
              ·
                refine ⟨39699087832162204168174165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52932117109549605557565553 39699087832162204168174165)
                ·
                  refine ⟨465223685533150830095791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39699087832162204168174165 465223685533150830095791)
                  ·
                    rfl

theorem cell23_8154179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 8].length) (baseStart_8154179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8154179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8154179 prefixEnd_8154179 := by exact prefixLift 8154179
  have htrace : WordTrace (prefixWord ++ tailWord_8154179) baseStart_8154179 baseEnd_8154179 := by
    simpa [prefixWord, tailWord_8154179, baseEnd_8154179] using wordTrace_append hprefix tailTrace_8154179
  have hstable : (prefixWord ++ tailWord_8154179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8154179).length < 2 ^ (prefixWord ++ tailWord_8154179).sum := by decide
  have hdescent : baseEnd_8154179 < baseStart_8154179 := by decide
  rcases family_descends (prefixWord ++ tailWord_8154179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8154213 : List Nat := [1, 3, 1, 3, 2, 1, 5, 1, 6]
def baseStart_8154213 : Nat := 118140960795 + 8154213 * 2 ^ 59
def prefixEnd_8154213 : Nat := 4983230072969 + 3 ^ 40 * 8154213 * 2
def baseEnd_8154213 : Nat := 465225625348956704204107

theorem tailTrace_8154213 : CollatzResearch.WordTrace tailWord_8154213 prefixEnd_8154213 465225625348956704204107 := by
  unfold tailWord_8154213
  simp only [CollatzResearch.WordTrace]
  refine ⟨297408581207686404552675293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198272387471790936368450195 297408581207686404552675293)
  ·
    refine ⟨111528217952882401707253235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297408581207686404552675293 111528217952882401707253235)
    ·
      refine ⟨167292326929323602560879853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111528217952882401707253235 167292326929323602560879853)
      ·
        refine ⟨62734622598496350960329945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167292326929323602560879853 62734622598496350960329945)
        ·
          refine ⟨47050966948872263220247459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62734622598496350960329945 47050966948872263220247459)
          ·
            refine ⟨70576450423308394830371189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47050966948872263220247459 70576450423308394830371189)
            ·
              refine ⟨6616542227185162015347299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70576450423308394830371189 6616542227185162015347299)
              ·
                refine ⟨9924813340777743023020949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6616542227185162015347299 9924813340777743023020949)
                ·
                  refine ⟨465225625348956704204107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9924813340777743023020949 465225625348956704204107)
                  ·
                    rfl

theorem cell23_8154213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 1, 6].length) (baseStart_8154213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8154213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8154213 prefixEnd_8154213 := by exact prefixLift 8154213
  have htrace : WordTrace (prefixWord ++ tailWord_8154213) baseStart_8154213 baseEnd_8154213 := by
    simpa [prefixWord, tailWord_8154213, baseEnd_8154213] using wordTrace_append hprefix tailTrace_8154213
  have hstable : (prefixWord ++ tailWord_8154213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8154213).length < 2 ^ (prefixWord ++ tailWord_8154213).sum := by decide
  have hdescent : baseEnd_8154213 < baseStart_8154213 := by decide
  rcases family_descends (prefixWord ++ tailWord_8154213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8154223 : List Nat := [1, 1, 2, 1, 3, 3, 1, 4, 3, 1, 3]
def baseStart_8154223 : Nat := 118140960795 + 8154223 * 2 ^ 59
def prefixEnd_8154223 : Nat := 4983230072969 + 3 ^ 40 * 8154223 * 2
def baseEnd_8154223 : Nat := 4187035762947155298711917

theorem tailTrace_8154223 : CollatzResearch.WordTrace tailWord_8154223 prefixEnd_8154223 4187035762947155298711917 := by
  unfold tailWord_8154223
  simp only [CollatzResearch.WordTrace]
  refine ⟨297408945937650176260539323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198272630625100117507026215 297408945937650176260539323)
  ·
    refine ⟨446113418906475264390808985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297408945937650176260539323 446113418906475264390808985)
    ·
      refine ⟨334585064179856448293106739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446113418906475264390808985 334585064179856448293106739)
      ·
        refine ⟨501877596269784672439660109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334585064179856448293106739 501877596269784672439660109)
        ·
          refine ⟨188204098601169252164872541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 501877596269784672439660109 188204098601169252164872541)
          ·
            refine ⟨70576536975438469561827203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188204098601169252164872541 70576536975438469561827203)
            ·
              refine ⟨105864805463157704342740805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70576536975438469561827203 105864805463157704342740805)
              ·
                refine ⟨19849651024342069564263901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105864805463157704342740805 19849651024342069564263901)
                ·
                  refine ⟨7443619134128276086598963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19849651024342069564263901 7443619134128276086598963)
                  ·
                    refine ⟨11165428701192414129898445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7443619134128276086598963 11165428701192414129898445)
                    ·
                      refine ⟨4187035762947155298711917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11165428701192414129898445 4187035762947155298711917)
                      ·
                        rfl

theorem cell23_8154223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 3, 1, 3].length) (baseStart_8154223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8154223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8154223 prefixEnd_8154223 := by exact prefixLift 8154223
  have htrace : WordTrace (prefixWord ++ tailWord_8154223) baseStart_8154223 baseEnd_8154223 := by
    simpa [prefixWord, tailWord_8154223, baseEnd_8154223] using wordTrace_append hprefix tailTrace_8154223
  have hstable : (prefixWord ++ tailWord_8154223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8154223).length < 2 ^ (prefixWord ++ tailWord_8154223).sum := by decide
  have hdescent : baseEnd_8154223 < baseStart_8154223 := by decide
  rcases family_descends (prefixWord ++ tailWord_8154223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8154250 : List Nat := [3, 1, 2, 3, 1, 1, 3, 2, 2, 3, 2]
def baseStart_8154250 : Nat := 118140960795 + 8154250 * 2 ^ 59
def prefixEnd_8154250 : Nat := 4983230072969 + 3 ^ 40 * 8154250 * 2
def baseEnd_8154250 : Nat := 4187049626924826693074293

theorem tailTrace_8154250 : CollatzResearch.WordTrace tailWord_8154250 prefixEnd_8154250 4187049626924826693074293 := by
  unfold tailWord_8154250
  simp only [CollatzResearch.WordTrace]
  refine ⟨74352482677138089967943051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198273287139034906581181469 74352482677138089967943051)
  ·
    refine ⟨111528724015707134951914577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74352482677138089967943051 111528724015707134951914577)
    ·
      refine ⟨83646543011780351213935933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111528724015707134951914577 83646543011780351213935933)
      ·
        refine ⟨31367453629417631705225975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83646543011780351213935933 31367453629417631705225975)
        ·
          refine ⟨47051180444126447557838963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31367453629417631705225975 47051180444126447557838963)
          ·
            refine ⟨70576770666189671336758445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47051180444126447557838963 70576770666189671336758445)
            ·
              refine ⟨26466288999821126751284417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70576770666189671336758445 26466288999821126751284417)
              ·
                refine ⟨19849716749865845063463313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26466288999821126751284417 19849716749865845063463313)
                ·
                  refine ⟨14887287562399383797597485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19849716749865845063463313 14887287562399383797597485)
                  ·
                    refine ⟨5582732835899768924099057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14887287562399383797597485 5582732835899768924099057)
                    ·
                      refine ⟨4187049626924826693074293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5582732835899768924099057 4187049626924826693074293)
                      ·
                        rfl

theorem cell23_8154250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_8154250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8154250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8154250 prefixEnd_8154250 := by exact prefixLift 8154250
  have htrace : WordTrace (prefixWord ++ tailWord_8154250) baseStart_8154250 baseEnd_8154250 := by
    simpa [prefixWord, tailWord_8154250, baseEnd_8154250] using wordTrace_append hprefix tailTrace_8154250
  have hstable : (prefixWord ++ tailWord_8154250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8154250).length < 2 ^ (prefixWord ++ tailWord_8154250).sum := by decide
  have hdescent : baseEnd_8154250 < baseStart_8154250 := by decide
  rcases family_descends (prefixWord ++ tailWord_8154250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8154300 : List Nat := [2, 2, 2, 3, 2, 3, 1, 1, 1, 1, 5]
def baseStart_8154300 : Nat := 118140960795 + 8154300 * 2 ^ 59
def prefixEnd_8154300 : Nat := 4983230072969 + 3 ^ 40 * 8154300 * 2
def baseEnd_8154300 : Nat := 4187075300957551497449063

theorem tailTrace_8154300 : CollatzResearch.WordTrace tailWord_8154300 prefixEnd_8154300 4187075300957551497449063 := by
  unfold tailWord_8154300
  simp only [CollatzResearch.WordTrace]
  refine ⟨148705877179185609205546177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198274502905580812274061569 148705877179185609205546177)
  ·
    refine ⟨111529407884389206904159633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148705877179185609205546177 111529407884389206904159633)
    ·
      refine ⟨83647055913291905178119725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111529407884389206904159633 83647055913291905178119725)
      ·
        refine ⟨31367645967484464441794897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83647055913291905178119725 31367645967484464441794897)
        ·
          refine ⟨23525734475613348331346173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31367645967484464441794897 23525734475613348331346173)
          ·
            refine ⟨8822150428355005624254815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23525734475613348331346173 8822150428355005624254815)
            ·
              refine ⟨13233225642532508436382223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8822150428355005624254815 13233225642532508436382223)
              ·
                refine ⟨19849838463798762654573335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13233225642532508436382223 19849838463798762654573335)
                ·
                  refine ⟨29774757695698143981860003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19849838463798762654573335 29774757695698143981860003)
                  ·
                    refine ⟨44662136543547215972790005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29774757695698143981860003 44662136543547215972790005)
                    ·
                      refine ⟨4187075300957551497449063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44662136543547215972790005 4187075300957551497449063)
                      ·
                        rfl

theorem cell23_8154300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_8154300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8154300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8154300 prefixEnd_8154300 := by exact prefixLift 8154300
  have htrace : WordTrace (prefixWord ++ tailWord_8154300) baseStart_8154300 baseEnd_8154300 := by
    simpa [prefixWord, tailWord_8154300, baseEnd_8154300] using wordTrace_append hprefix tailTrace_8154300
  have hstable : (prefixWord ++ tailWord_8154300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8154300).length < 2 ^ (prefixWord ++ tailWord_8154300).sum := by decide
  have hdescent : baseEnd_8154300 < baseStart_8154300 := by decide
  rcases family_descends (prefixWord ++ tailWord_8154300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8154308 : List Nat := [2, 3, 3, 1, 4, 1, 2, 2, 1, 1, 3]
def baseStart_8154308 : Nat := 118140960795 + 8154308 * 2 ^ 59
def prefixEnd_8154308 : Nat := 4983230072969 + 3 ^ 40 * 8154308 * 2
def baseEnd_8154308 : Nat := 4187079408802787466149027

theorem tailTrace_8154308 : CollatzResearch.WordTrace tailWord_8154308 prefixEnd_8154308 4187079408802787466149027 := by
  unfold tailWord_8154308
  simp only [CollatzResearch.WordTrace]
  refine ⟨148706023071171117888691789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198274697428228157184922385 148706023071171117888691789)
  ·
    refine ⟨55764758651689169208259421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148706023071171117888691789 55764758651689169208259421)
    ·
      refine ⟨20911784494383438453097283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55764758651689169208259421 20911784494383438453097283)
      ·
        refine ⟨31367676741575157679645925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20911784494383438453097283 31367676741575157679645925)
        ·
          refine ⟨5881439389045342064933611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31367676741575157679645925 5881439389045342064933611)
          ·
            refine ⟨8822159083568013097400417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5881439389045342064933611 8822159083568013097400417)
            ·
              refine ⟨6616619312676009823050313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8822159083568013097400417 6616619312676009823050313)
              ·
                refine ⟨4962464484507007367287735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6616619312676009823050313 4962464484507007367287735)
                ·
                  refine ⟨7443696726760511050931603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4962464484507007367287735 7443696726760511050931603)
                  ·
                    refine ⟨11165545090140766576397405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7443696726760511050931603 11165545090140766576397405)
                    ·
                      refine ⟨4187079408802787466149027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11165545090140766576397405 4187079408802787466149027)
                      ·
                        rfl

theorem cell23_8154308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_8154308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8154308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8154308 prefixEnd_8154308 := by exact prefixLift 8154308
  have htrace : WordTrace (prefixWord ++ tailWord_8154308) baseStart_8154308 baseEnd_8154308 := by
    simpa [prefixWord, tailWord_8154308, baseEnd_8154308] using wordTrace_append hprefix tailTrace_8154308
  have hstable : (prefixWord ++ tailWord_8154308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8154308).length < 2 ^ (prefixWord ++ tailWord_8154308).sum := by decide
  have hdescent : baseEnd_8154308 < baseStart_8154308 := by decide
  rcases family_descends (prefixWord ++ tailWord_8154308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8154313 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 8, 1, 3]
def baseStart_8154313 : Nat := 118140960795 + 8154313 * 2 ^ 59
def prefixEnd_8154313 : Nat := 4983230072969 + 3 ^ 40 * 8154313 * 2
def baseEnd_8154313 : Nat := 4187081976206059946586503

theorem tailTrace_8154313 : CollatzResearch.WordTrace tailWord_8154313 prefixEnd_8154313 4187081976206059946586503 := by
  unfold tailWord_8154313
  simp only [CollatzResearch.WordTrace]
  refine ⟨297412228507324121631315593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198274819004882747754210395 297412228507324121631315593)
  ·
    refine ⟨223059171380493091223486695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297412228507324121631315593 223059171380493091223486695)
    ·
      refine ⟨334588757070739636835230043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223059171380493091223486695 334588757070739636835230043)
      ·
        refine ⟨501883135606109455252845065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334588757070739636835230043 501883135606109455252845065)
        ·
          refine ⟨376412351704582091439633799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 501883135606109455252845065 376412351704582091439633799)
          ·
            refine ⟨564618527556873137159450699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376412351704582091439633799 564618527556873137159450699)
            ·
              refine ⟨846927791335309705739176049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 564618527556873137159450699 846927791335309705739176049)
              ·
                refine ⟨635195843501482279304382037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 846927791335309705739176049 635195843501482279304382037)
                ·
                  refine ⟨7443701291032995460598227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 635195843501482279304382037 7443701291032995460598227)
                  ·
                    refine ⟨11165551936549493190897341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7443701291032995460598227 11165551936549493190897341)
                    ·
                      refine ⟨4187081976206059946586503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11165551936549493190897341 4187081976206059946586503)
                      ·
                        rfl

theorem cell23_8154313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 8, 1, 3].length) (baseStart_8154313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8154313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8154313 prefixEnd_8154313 := by exact prefixLift 8154313
  have htrace : WordTrace (prefixWord ++ tailWord_8154313) baseStart_8154313 baseEnd_8154313 := by
    simpa [prefixWord, tailWord_8154313, baseEnd_8154313] using wordTrace_append hprefix tailTrace_8154313
  have hstable : (prefixWord ++ tailWord_8154313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8154313).length < 2 ^ (prefixWord ++ tailWord_8154313).sum := by decide
  have hdescent : baseEnd_8154313 < baseStart_8154313 := by decide
  rcases family_descends (prefixWord ++ tailWord_8154313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8154314 : List Nat := [3, 1, 2, 1, 3, 3, 1, 4, 1, 2, 2]
def baseStart_8154314 : Nat := 118140960795 + 8154314 * 2 ^ 59
def prefixEnd_8154314 : Nat := 4983230072969 + 3 ^ 40 * 8154314 * 2
def baseEnd_8154314 : Nat := 4187082489686714442673999

theorem tailTrace_8154314 : CollatzResearch.WordTrace tailWord_8154314 prefixEnd_8154314 4187082489686714442673999 := by
  unfold tailWord_8154314
  simp only [CollatzResearch.WordTrace]
  refine ⟨74353066245080124700525499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198274843320213665868067997 74353066245080124700525499)
  ·
    refine ⟨111529599367620187050788249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74353066245080124700525499 111529599367620187050788249)
    ·
      refine ⟨83647199525715140288091187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111529599367620187050788249 83647199525715140288091187)
      ·
        refine ⟨125470799288572710432136781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83647199525715140288091187 125470799288572710432136781)
        ·
          refine ⟨47051549733214766412051293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125470799288572710432136781 47051549733214766412051293)
          ·
            refine ⟨17644331149955537404519235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47051549733214766412051293 17644331149955537404519235)
            ·
              refine ⟨26466496724933306106778853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17644331149955537404519235 26466496724933306106778853)
              ·
                refine ⟨4962468135924994895021035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26466496724933306106778853 4962468135924994895021035)
                ·
                  refine ⟨7443702203887492342531553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4962468135924994895021035 7443702203887492342531553)
                  ·
                    refine ⟨5582776652915619256898665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7443702203887492342531553 5582776652915619256898665)
                    ·
                      refine ⟨4187082489686714442673999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5582776652915619256898665 4187082489686714442673999)
                      ·
                        rfl

theorem cell23_8154314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 4, 1, 2, 2].length) (baseStart_8154314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8154314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8154314 prefixEnd_8154314 := by exact prefixLift 8154314
  have htrace : WordTrace (prefixWord ++ tailWord_8154314) baseStart_8154314 baseEnd_8154314 := by
    simpa [prefixWord, tailWord_8154314, baseEnd_8154314] using wordTrace_append hprefix tailTrace_8154314
  have hstable : (prefixWord ++ tailWord_8154314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8154314).length < 2 ^ (prefixWord ++ tailWord_8154314).sum := by decide
  have hdescent : baseEnd_8154314 < baseStart_8154314 := by decide
  rcases family_descends (prefixWord ++ tailWord_8154314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8154340 : List Nat := [2, 3, 1, 1, 1, 2, 4, 1, 3, 3, 2]
def baseStart_8154340 : Nat := 118140960795 + 8154340 * 2 ^ 59
def prefixEnd_8154340 : Nat := 4983230072969 + 3 ^ 40 * 8154340 * 2
def baseEnd_8154340 : Nat := 4187095840183731340948879

theorem tailTrace_8154340 : CollatzResearch.WordTrace tailWord_8154340 prefixEnd_8154340 4187095840183731340948879 := by
  unfold tailWord_8154340
  simp only [CollatzResearch.WordTrace]
  refine ⟨148706606639113152621274237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198275475518817536828365649 148706606639113152621274237)
  ·
    refine ⟨55764977489667432232977839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148706606639113152621274237 55764977489667432232977839)
    ·
      refine ⟨83647466234501148349466759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55764977489667432232977839 83647466234501148349466759)
      ·
        refine ⟨125471199351751722524200139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83647466234501148349466759 125471199351751722524200139)
        ·
          refine ⟨188206799027627583786300209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125471199351751722524200139 188206799027627583786300209)
          ·
            refine ⟨141155099270720687839725157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188206799027627583786300209 141155099270720687839725157)
            ·
              refine ⟨26466581113260128969948467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141155099270720687839725157 26466581113260128969948467)
              ·
                refine ⟨39699871669890193454922701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26466581113260128969948467 39699871669890193454922701)
                ·
                  refine ⟨14887451876208822545596013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39699871669890193454922701 14887451876208822545596013)
                  ·
                    refine ⟨5582794453578308454598505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14887451876208822545596013 5582794453578308454598505)
                    ·
                      refine ⟨4187095840183731340948879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5582794453578308454598505 4187095840183731340948879)
                      ·
                        rfl

theorem cell23_8154340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 3, 3, 2].length) (baseStart_8154340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8154340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8154340 prefixEnd_8154340 := by exact prefixLift 8154340
  have htrace : WordTrace (prefixWord ++ tailWord_8154340) baseStart_8154340 baseEnd_8154340 := by
    simpa [prefixWord, tailWord_8154340, baseEnd_8154340] using wordTrace_append hprefix tailTrace_8154340
  have hstable : (prefixWord ++ tailWord_8154340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8154340).length < 2 ^ (prefixWord ++ tailWord_8154340).sum := by decide
  have hdescent : baseEnd_8154340 < baseStart_8154340 := by decide
  rcases family_descends (prefixWord ++ tailWord_8154340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8154364 : List Nat := [2, 2, 2, 1, 5, 2, 1, 2, 2, 1, 3]
def baseStart_8154364 : Nat := 118140960795 + 8154364 * 2 ^ 59
def prefixEnd_8154364 : Nat := 4983230072969 + 3 ^ 40 * 8154364 * 2
def baseEnd_8154364 : Nat := 4187108163719439247048769

theorem tailTrace_8154364 : CollatzResearch.WordTrace tailWord_8154364 prefixEnd_8154364 4187108163719439247048769 := by
  unfold tailWord_8154364
  simp only [CollatzResearch.WordTrace]
  refine ⟨148707044315069678670711073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198276059086759571560948097 148707044315069678670711073)
  ·
    refine ⟨111530283236302259003033305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148707044315069678670711073 111530283236302259003033305)
    ·
      refine ⟨83647712427226694252274979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111530283236302259003033305 83647712427226694252274979)
      ·
        refine ⟨125471568640840041378412469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83647712427226694252274979 125471568640840041378412469)
        ·
          refine ⟨11762959560078753879226169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125471568640840041378412469 11762959560078753879226169)
          ·
            refine ⟨8822219670059065409419627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11762959560078753879226169 8822219670059065409419627)
            ·
              refine ⟨13233329505088598114129441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8822219670059065409419627 13233329505088598114129441)
              ·
                refine ⟨9924997128816448585597081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13233329505088598114129441 9924997128816448585597081)
                ·
                  refine ⟨7443747846612336439197811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9924997128816448585597081 7443747846612336439197811)
                  ·
                    refine ⟨11165621769918504658796717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7443747846612336439197811 11165621769918504658796717)
                    ·
                      refine ⟨4187108163719439247048769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11165621769918504658796717 4187108163719439247048769)
                      ·
                        rfl

theorem cell23_8154364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 2, 2, 1, 3].length) (baseStart_8154364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8154364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8154364 prefixEnd_8154364 := by exact prefixLift 8154364
  have htrace : WordTrace (prefixWord ++ tailWord_8154364) baseStart_8154364 baseEnd_8154364 := by
    simpa [prefixWord, tailWord_8154364, baseEnd_8154364] using wordTrace_append hprefix tailTrace_8154364
  have hstable : (prefixWord ++ tailWord_8154364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8154364).length < 2 ^ (prefixWord ++ tailWord_8154364).sum := by decide
  have hdescent : baseEnd_8154364 < baseStart_8154364 := by decide
  rcases family_descends (prefixWord ++ tailWord_8154364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8154478 : List Nat := [4, 1, 2, 4, 2, 1, 2, 2, 5]
def baseStart_8154478 : Nat := 118140960795 + 8154478 * 2 ^ 59
def prefixEnd_8154478 : Nat := 4983230072969 + 3 ^ 40 * 8154478 * 2
def baseEnd_8154478 : Nat := 465240744501561311224805

theorem tailTrace_8154478 : CollatzResearch.WordTrace tailWord_8154478 prefixEnd_8154478 465240744501561311224805 := by
  unfold tailWord_8154478
  simp only [CollatzResearch.WordTrace]
  refine ⟨37177280818965794351384011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198278831034484236540714725 37177280818965794351384011)
  ·
    refine ⟨55765921228448691527076017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37177280818965794351384011 55765921228448691527076017)
    ·
      refine ⟨41824440921336518645307013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55765921228448691527076017 41824440921336518645307013)
      ·
        refine ⟨7842082672750597245995065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41824440921336518645307013 7842082672750597245995065)
        ·
          refine ⟨5881562004562947934496299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7842082672750597245995065 5881562004562947934496299)
          ·
            refine ⟨8822343006844421901744449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5881562004562947934496299 8822343006844421901744449)
            ·
              refine ⟨6616757255133316426308337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8822343006844421901744449 6616757255133316426308337)
              ·
                refine ⟨4962567941349987319731253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6616757255133316426308337 4962567941349987319731253)
                ·
                  refine ⟨465240744501561311224805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4962567941349987319731253 465240744501561311224805)
                  ·
                    rfl

theorem cell23_8154478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 2, 5].length) (baseStart_8154478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8154478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8154478 prefixEnd_8154478 := by exact prefixLift 8154478
  have htrace : WordTrace (prefixWord ++ tailWord_8154478) baseStart_8154478 baseEnd_8154478 := by
    simpa [prefixWord, tailWord_8154478, baseEnd_8154478] using wordTrace_append hprefix tailTrace_8154478
  have hstable : (prefixWord ++ tailWord_8154478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8154478).length < 2 ^ (prefixWord ++ tailWord_8154478).sum := by decide
  have hdescent : baseEnd_8154478 < baseStart_8154478 := by decide
  rcases family_descends (prefixWord ++ tailWord_8154478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8154480 : List Nat := [2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 3]
def baseStart_8154480 : Nat := 118140960795 + 8154480 * 2 ^ 59
def prefixEnd_8154480 : Nat := 4983230072969 + 3 ^ 40 * 8154480 * 2
def baseEnd_8154480 : Nat := 4187167727475360793198235

theorem tailTrace_8154480 : CollatzResearch.WordTrace tailWord_8154480 prefixEnd_8154480 4187167727475360793198235 := by
  unfold tailWord_8154480
  simp only [CollatzResearch.WordTrace]
  refine ⟨148709159748859554576322447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198278879665146072768429929 148709159748859554576322447)
  ·
    refine ⟨223063739623289331864483671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148709159748859554576322447 223063739623289331864483671)
    ·
      refine ⟨334595609434933997796725507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223063739623289331864483671 334595609434933997796725507)
      ·
        refine ⟨501893414152400996695088261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334595609434933997796725507 501893414152400996695088261)
        ·
          refine ⟨94105015153575186880329049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 501893414152400996695088261 94105015153575186880329049)
          ·
            refine ⟨70578761365181390160246787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94105015153575186880329049 70578761365181390160246787)
            ·
              refine ⟨105868142047772085240370181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70578761365181390160246787 105868142047772085240370181)
              ·
                refine ⟨19850276633957265982569409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105868142047772085240370181 19850276633957265982569409)
                ·
                  refine ⟨14887707475467949486927057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19850276633957265982569409 14887707475467949486927057)
                  ·
                    refine ⟨11165780606600962115195293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14887707475467949486927057 11165780606600962115195293)
                    ·
                      refine ⟨4187167727475360793198235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11165780606600962115195293 4187167727475360793198235)
                      ·
                        rfl

theorem cell23_8154480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 3].length) (baseStart_8154480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8154480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8154480 prefixEnd_8154480 := by exact prefixLift 8154480
  have htrace : WordTrace (prefixWord ++ tailWord_8154480) baseStart_8154480 baseEnd_8154480 := by
    simpa [prefixWord, tailWord_8154480, baseEnd_8154480] using wordTrace_append hprefix tailTrace_8154480
  have hstable : (prefixWord ++ tailWord_8154480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8154480).length < 2 ^ (prefixWord ++ tailWord_8154480).sum := by decide
  have hdescent : baseEnd_8154480 < baseStart_8154480 := by decide
  rcases family_descends (prefixWord ++ tailWord_8154480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8154487 : List Nat := [1, 1, 3, 1, 1, 2, 5, 4, 1, 4]
def baseStart_8154487 : Nat := 118140960795 + 8154487 * 2 ^ 59
def prefixEnd_8154487 : Nat := 4983230072969 + 3 ^ 40 * 8154487 * 2
def baseEnd_8154487 : Nat := 1395723773946647421936901

theorem tailTrace_8154487 : CollatzResearch.WordTrace tailWord_8154487 prefixEnd_8154487 1395723773946647421936901 := by
  unfold tailWord_8154487
  simp only [CollatzResearch.WordTrace]
  refine ⟨297418574808693749348149715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198279049872462499565433143 297418574808693749348149715)
  ·
    refine ⟨446127862213040624022224573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297418574808693749348149715 446127862213040624022224573)
    ·
      refine ⟨167297948329890234008334215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 446127862213040624022224573 167297948329890234008334215)
      ·
        refine ⟨250946922494835351012501323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167297948329890234008334215 250946922494835351012501323)
        ·
          refine ⟨376420383742253026518751985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250946922494835351012501323 376420383742253026518751985)
          ·
            refine ⟨282315287806689769889063989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 376420383742253026518751985 282315287806689769889063989)
            ·
              refine ⟨26467058231877165927099749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 282315287806689769889063989 26467058231877165927099749)
              ·
                refine ⟨4962573418476968611331203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26467058231877165927099749 4962573418476968611331203)
                ·
                  refine ⟨7443860127715452916996805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4962573418476968611331203 7443860127715452916996805)
                  ·
                    refine ⟨1395723773946647421936901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7443860127715452916996805 1395723773946647421936901)
                    ·
                      rfl

theorem cell23_8154487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 4, 1, 4].length) (baseStart_8154487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8154487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8154487 prefixEnd_8154487 := by exact prefixLift 8154487
  have htrace : WordTrace (prefixWord ++ tailWord_8154487) baseStart_8154487 baseEnd_8154487 := by
    simpa [prefixWord, tailWord_8154487, baseEnd_8154487] using wordTrace_append hprefix tailTrace_8154487
  have hstable : (prefixWord ++ tailWord_8154487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8154487).length < 2 ^ (prefixWord ++ tailWord_8154487).sum := by decide
  have hdescent : baseEnd_8154487 < baseStart_8154487 := by decide
  rcases family_descends (prefixWord ++ tailWord_8154487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8154500 : List Nat := [2, 3, 2, 1, 1, 3, 2, 3, 6]
def baseStart_8154500 : Nat := 118140960795 + 8154500 * 2 ^ 59
def prefixEnd_8154500 : Nat := 4983230072969 + 3 ^ 40 * 8154500 * 2
def baseEnd_8154500 : Nat := 465241999676494523883127

theorem tailTrace_8154500 : CollatzResearch.WordTrace tailWord_8154500 prefixEnd_8154500 465241999676494523883127 := by
  unfold tailWord_8154500
  simp only [CollatzResearch.WordTrace]
  refine ⟨148709524478823326284186477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198279365971764435045581969 148709524478823326284186477)
  ·
    refine ⟨55766071679558747356569929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148709524478823326284186477 55766071679558747356569929)
    ·
      refine ⟨41824553759669060517427447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55766071679558747356569929 41824553759669060517427447)
      ·
        refine ⟨62736830639503590776141171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41824553759669060517427447 62736830639503590776141171)
        ·
          refine ⟨94105245959255386164211757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62736830639503590776141171 94105245959255386164211757)
          ·
            refine ⟨35289467234720769811579409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94105245959255386164211757 35289467234720769811579409)
            ·
              refine ⟨26467100426040577358684557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35289467234720769811579409 26467100426040577358684557)
              ·
                refine ⟨9925162659765216509506709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26467100426040577358684557 9925162659765216509506709)
                ·
                  refine ⟨465241999676494523883127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9925162659765216509506709 465241999676494523883127)
                  ·
                    rfl

theorem cell23_8154500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 3, 6].length) (baseStart_8154500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8154500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8154500 prefixEnd_8154500 := by exact prefixLift 8154500
  have htrace : WordTrace (prefixWord ++ tailWord_8154500) baseStart_8154500 baseEnd_8154500 := by
    simpa [prefixWord, tailWord_8154500, baseEnd_8154500] using wordTrace_append hprefix tailTrace_8154500
  have hstable : (prefixWord ++ tailWord_8154500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8154500).length < 2 ^ (prefixWord ++ tailWord_8154500).sum := by decide
  have hdescent : baseEnd_8154500 < baseStart_8154500 := by decide
  rcases family_descends (prefixWord ++ tailWord_8154500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8154514 : List Nat := [3, 2, 3, 3, 1, 1, 1, 1, 1, 4, 3]
def baseStart_8154514 : Nat := 118140960795 + 8154514 * 2 ^ 59
def prefixEnd_8154514 : Nat := 4983230072969 + 3 ^ 40 * 8154514 * 2
def baseEnd_8154514 : Nat := 4187185185817613660173079

theorem tailTrace_8154514 : CollatzResearch.WordTrace tailWord_8154514 prefixEnd_8154514 4187185185817613660173079 := by
  unfold tailWord_8154514
  simp only [CollatzResearch.WordTrace]
  refine ⟨74354889894898983239845649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198279706386397288639588397 74354889894898983239845649)
  ·
    refine ⟨55766167421174237429884237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74354889894898983239845649 55766167421174237429884237)
    ·
      refine ⟨20912312782940339036206589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55766167421174237429884237 20912312782940339036206589)
      ·
        refine ⟨7842117293602627138577471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20912312782940339036206589 7842117293602627138577471)
        ·
          refine ⟨11763175940403940707866207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7842117293602627138577471 11763175940403940707866207)
          ·
            refine ⟨17644763910605911061799311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11763175940403940707866207 17644763910605911061799311)
            ·
              refine ⟨26467145865908866592698967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17644763910605911061799311 26467145865908866592698967)
              ·
                refine ⟨39700718798863299889048451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26467145865908866592698967 39700718798863299889048451)
                ·
                  refine ⟨59551078198294949833572677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39700718798863299889048451 59551078198294949833572677)
                  ·
                    refine ⟨11165827162180303093794877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59551078198294949833572677 11165827162180303093794877)
                    ·
                      refine ⟨4187185185817613660173079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11165827162180303093794877 4187185185817613660173079)
                      ·
                        rfl

theorem cell23_8154514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_8154514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8154514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8154514 prefixEnd_8154514 := by exact prefixLift 8154514
  have htrace : WordTrace (prefixWord ++ tailWord_8154514) baseStart_8154514 baseEnd_8154514 := by
    simpa [prefixWord, tailWord_8154514, baseEnd_8154514] using wordTrace_append hprefix tailTrace_8154514
  have hstable : (prefixWord ++ tailWord_8154514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8154514).length < 2 ^ (prefixWord ++ tailWord_8154514).sum := by decide
  have hdescent : baseEnd_8154514 < baseStart_8154514 := by decide
  rcases family_descends (prefixWord ++ tailWord_8154514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8154543 : List Nat := [1, 1, 2, 1, 2, 2, 1, 4, 3, 6]
def baseStart_8154543 : Nat := 118140960795 + 8154543 * 2 ^ 59
def prefixEnd_8154543 : Nat := 4983230072969 + 3 ^ 40 * 8154543 * 2
def baseEnd_8154543 : Nat := 1395733358918864682236815

theorem tailTrace_8154543 : CollatzResearch.WordTrace tailWord_8154543 prefixEnd_8154543 1395733358918864682236815 := by
  unfold tailWord_8154543
  simp only [CollatzResearch.WordTrace]
  refine ⟨297420617296490870912188283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198280411530993913941458855 297420617296490870912188283)
  ·
    refine ⟨446130925944736306368282425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297420617296490870912188283 446130925944736306368282425)
    ·
      refine ⟨334598194458552229776211819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446130925944736306368282425 334598194458552229776211819)
      ·
        refine ⟨501897291687828344664317729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334598194458552229776211819 501897291687828344664317729)
        ·
          refine ⟨376422968765871258498238297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 501897291687828344664317729 376422968765871258498238297)
          ·
            refine ⟨282317226574403443873678723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 376422968765871258498238297 282317226574403443873678723)
            ·
              refine ⟨423475839861605165810518085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282317226574403443873678723 423475839861605165810518085)
              ·
                refine ⟨79401719974050968589472141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 423475839861605165810518085 79401719974050968589472141)
                ·
                  refine ⟨29775644990269113221052053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79401719974050968589472141 29775644990269113221052053)
                  ·
                    refine ⟨1395733358918864682236815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29775644990269113221052053 1395733358918864682236815)
                    ·
                      rfl

theorem cell23_8154543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 6].length) (baseStart_8154543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8154543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8154543 prefixEnd_8154543 := by exact prefixLift 8154543
  have htrace : WordTrace (prefixWord ++ tailWord_8154543) baseStart_8154543 baseEnd_8154543 := by
    simpa [prefixWord, tailWord_8154543, baseEnd_8154543] using wordTrace_append hprefix tailTrace_8154543
  have hstable : (prefixWord ++ tailWord_8154543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8154543).length < 2 ^ (prefixWord ++ tailWord_8154543).sum := by decide
  have hdescent : baseEnd_8154543 < baseStart_8154543 := by decide
  rcases family_descends (prefixWord ++ tailWord_8154543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8154560 : List Nat := [2, 1, 1, 2, 3, 1, 5, 1, 1, 6]
def baseStart_8154560 : Nat := 118140960795 + 8154560 * 2 ^ 59
def prefixEnd_8154560 : Nat := 4983230072969 + 3 ^ 40 * 8154560 * 2
def baseEnd_8154560 : Nat := 1395736268642573493399289

theorem tailTrace_8154560 : CollatzResearch.WordTrace tailWord_8154560 prefixEnd_8154560 1395736268642573493399289 := by
  unfold tailWord_8154560
  simp only [CollatzResearch.WordTrace]
  refine ⟨148710618668714641407778567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198280824891619521877038089 148710618668714641407778567)
  ·
    refine ⟨223065928003071962111667851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148710618668714641407778567 223065928003071962111667851)
    ·
      refine ⟨334598892004607943167501777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223065928003071962111667851 334598892004607943167501777)
      ·
        refine ⟨250949169003455957375626333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334598892004607943167501777 250949169003455957375626333)
        ·
          refine ⟨94105938376295984015859875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250949169003455957375626333 94105938376295984015859875)
          ·
            refine ⟨141158907564443976023789813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94105938376295984015859875 141158907564443976023789813)
            ·
              refine ⟨13233647584166622752230295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141158907564443976023789813 13233647584166622752230295)
              ·
                refine ⟨19850471376249934128345443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13233647584166622752230295 19850471376249934128345443)
                ·
                  refine ⟨29775707064374901192518165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19850471376249934128345443 29775707064374901192518165)
                  ·
                    refine ⟨1395736268642573493399289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29775707064374901192518165 1395736268642573493399289)
                    ·
                      rfl

theorem cell23_8154560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 1, 6].length) (baseStart_8154560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8154560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8154560 prefixEnd_8154560 := by exact prefixLift 8154560
  have htrace : WordTrace (prefixWord ++ tailWord_8154560) baseStart_8154560 baseEnd_8154560 := by
    simpa [prefixWord, tailWord_8154560, baseEnd_8154560] using wordTrace_append hprefix tailTrace_8154560
  have hstable : (prefixWord ++ tailWord_8154560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8154560).length < 2 ^ (prefixWord ++ tailWord_8154560).sum := by decide
  have hdescent : baseEnd_8154560 < baseStart_8154560 := by decide
  rcases family_descends (prefixWord ++ tailWord_8154560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8154564 : List Nat := [2, 3, 3, 2, 1, 2, 2, 2, 1, 5]
def baseStart_8154564 : Nat := 118140960795 + 8154564 * 2 ^ 59
def prefixEnd_8154564 : Nat := 4983230072969 + 3 ^ 40 * 8154564 * 2
def baseEnd_8154564 : Nat := 1395736953283446154849283

theorem tailTrace_8154564 : CollatzResearch.WordTrace tailWord_8154564 prefixEnd_8154564 1395736953283446154849283 := by
  unfold tailWord_8154564
  simp only [CollatzResearch.WordTrace]
  refine ⟨148710691614707395749351373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198280922152943194332468497 148710691614707395749351373)
  ·
    refine ⟨55766509355515273406006765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148710691614707395749351373 55766509355515273406006765)
    ·
      refine ⟨20912441008318227527252537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55766509355515273406006765 20912441008318227527252537)
      ·
        refine ⟨15684330756238670645439403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20912441008318227527252537 15684330756238670645439403)
        ·
          refine ⟨23526496134358005968159105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15684330756238670645439403 23526496134358005968159105)
          ·
            refine ⟨17644872100768504476119329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23526496134358005968159105 17644872100768504476119329)
            ·
              refine ⟨13233654075576378357089497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17644872100768504476119329 13233654075576378357089497)
              ·
                refine ⟨9925240556682283767817123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13233654075576378357089497 9925240556682283767817123)
                ·
                  refine ⟨14887860835023425651725685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9925240556682283767817123 14887860835023425651725685)
                  ·
                    refine ⟨1395736953283446154849283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14887860835023425651725685 1395736953283446154849283)
                    ·
                      rfl

theorem cell23_8154564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_8154564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8154564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8154564 prefixEnd_8154564 := by exact prefixLift 8154564
  have htrace : WordTrace (prefixWord ++ tailWord_8154564) baseStart_8154564 baseEnd_8154564 := by
    simpa [prefixWord, tailWord_8154564, baseEnd_8154564] using wordTrace_append hprefix tailTrace_8154564
  have hstable : (prefixWord ++ tailWord_8154564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8154564).length < 2 ^ (prefixWord ++ tailWord_8154564).sum := by decide
  have hdescent : baseEnd_8154564 < baseStart_8154564 := by decide
  rcases family_descends (prefixWord ++ tailWord_8154564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8154567 : List Nat := [1, 1, 4, 1, 1, 3, 4, 2, 1, 1, 4]
def baseStart_8154567 : Nat := 118140960795 + 8154567 * 2 ^ 59
def prefixEnd_8154567 : Nat := 4983230072969 + 3 ^ 40 * 8154567 * 2
def baseEnd_8154567 : Nat := 4187212400292301952810335

theorem tailTrace_8154567 : CollatzResearch.WordTrace tailWord_8154567 prefixEnd_8154567 4187212400292301952810335 := by
  unfold tailWord_8154567
  simp only [CollatzResearch.WordTrace]
  refine ⟨297421492648403923011061955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198280995098935948674041303 297421492648403923011061955)
  ·
    refine ⟨446132238972605884516592933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297421492648403923011061955 446132238972605884516592933)
    ·
      refine ⟨83649794807363603346861175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 446132238972605884516592933 83649794807363603346861175)
      ·
        refine ⟨125474692211045405020291763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83649794807363603346861175 125474692211045405020291763)
        ·
          refine ⟨188212038316568107530437645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125474692211045405020291763 188212038316568107530437645)
          ·
            refine ⟨70579514368713040323914117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188212038316568107530437645 70579514368713040323914117)
            ·
              refine ⟨13233658944133695060733897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70579514368713040323914117 13233658944133695060733897)
              ·
                refine ⟨9925244208100271295550423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13233658944133695060733897 9925244208100271295550423)
                ·
                  refine ⟨14887866312150406943325635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9925244208100271295550423 14887866312150406943325635)
                  ·
                    refine ⟨22331799468225610414988453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14887866312150406943325635 22331799468225610414988453)
                    ·
                      refine ⟨4187212400292301952810335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22331799468225610414988453 4187212400292301952810335)
                      ·
                        rfl

theorem cell23_8154567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 2, 1, 1, 4].length) (baseStart_8154567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8154567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8154567 prefixEnd_8154567 := by exact prefixLift 8154567
  have htrace : WordTrace (prefixWord ++ tailWord_8154567) baseStart_8154567 baseEnd_8154567 := by
    simpa [prefixWord, tailWord_8154567, baseEnd_8154567] using wordTrace_append hprefix tailTrace_8154567
  have hstable : (prefixWord ++ tailWord_8154567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8154567).length < 2 ^ (prefixWord ++ tailWord_8154567).sum := by decide
  have hdescent : baseEnd_8154567 < baseStart_8154567 := by decide
  rcases family_descends (prefixWord ++ tailWord_8154567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8154650 : List Nat := [3, 1, 1, 3, 1, 1, 1, 4, 2, 6]
def baseStart_8154650 : Nat := 118140960795 + 8154650 * 2 ^ 59
def prefixEnd_8154650 : Nat := 4983230072969 + 3 ^ 40 * 8154650 * 2
def baseEnd_8154650 : Nat := 1395751673062208376024151

theorem tailTrace_8154650 : CollatzResearch.WordTrace tailWord_8154650 prefixEnd_8154650 1395751673062208376024151 := by
  unfold tailWord_8154650
  simp only [CollatzResearch.WordTrace]
  refine ⟨74356129976775807046583351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198283013271402152124222269 74356129976775807046583351)
  ·
    refine ⟨111534194965163710569875027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74356129976775807046583351 111534194965163710569875027)
    ·
      refine ⟨167301292447745565854812541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111534194965163710569875027 167301292447745565854812541)
      ·
        refine ⟨62737984667904587195554703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167301292447745565854812541 62737984667904587195554703)
        ·
          refine ⟨94106977001856880793332055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62737984667904587195554703 94106977001856880793332055)
          ·
            refine ⟨141160465502785321189998083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94106977001856880793332055 141160465502785321189998083)
            ·
              refine ⟨211740698254177981784997125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141160465502785321189998083 211740698254177981784997125)
              ·
                refine ⟨39701380922658371584686961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 211740698254177981784997125 39701380922658371584686961)
                ·
                  refine ⟨29776035691993778688515221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39701380922658371584686961 29776035691993778688515221)
                  ·
                    refine ⟨1395751673062208376024151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29776035691993778688515221 1395751673062208376024151)
                    ·
                      rfl

theorem cell23_8154650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 2, 6].length) (baseStart_8154650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8154650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8154650 prefixEnd_8154650 := by exact prefixLift 8154650
  have htrace : WordTrace (prefixWord ++ tailWord_8154650) baseStart_8154650 baseEnd_8154650 := by
    simpa [prefixWord, tailWord_8154650, baseEnd_8154650] using wordTrace_append hprefix tailTrace_8154650
  have hstable : (prefixWord ++ tailWord_8154650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8154650).length < 2 ^ (prefixWord ++ tailWord_8154650).sum := by decide
  have hdescent : baseEnd_8154650 < baseStart_8154650 := by decide
  rcases family_descends (prefixWord ++ tailWord_8154650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8154674 : List Nat := [3, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2]
def baseStart_8154674 : Nat := 118140960795 + 8154674 * 2 ^ 59
def prefixEnd_8154674 : Nat := 4983230072969 + 3 ^ 40 * 8154674 * 2
def baseEnd_8154674 : Nat := 4187267342722333034172343

theorem tailTrace_8154674 : CollatzResearch.WordTrace tailWord_8154674 prefixEnd_8154674 4187267342722333034172343 := by
  unfold tailWord_8154674
  simp only [CollatzResearch.WordTrace]
  refine ⟨74356348814754070071301769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198283596839344186856804717 74356348814754070071301769)
  ·
    refine ⟨55767261611065552553476327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74356348814754070071301769 55767261611065552553476327)
    ·
      refine ⟨83650892416598328830214491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55767261611065552553476327 83650892416598328830214491)
      ·
        refine ⟨125476338624897493245321737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83650892416598328830214491 125476338624897493245321737)
        ·
          refine ⟨94107253968673119933991303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125476338624897493245321737 94107253968673119933991303)
          ·
            refine ⟨141160880953009679900986955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94107253968673119933991303 141160880953009679900986955)
            ·
              refine ⟨211741321429514519851480433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141160880953009679900986955 211741321429514519851480433)
              ·
                refine ⟨158805991072135889888610325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211741321429514519851480433 158805991072135889888610325)
                ·
                  refine ⟨7444030831506369838528609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 158805991072135889888610325 7444030831506369838528609)
                  ·
                    refine ⟨5583023123629777378896457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7444030831506369838528609 5583023123629777378896457)
                    ·
                      refine ⟨4187267342722333034172343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5583023123629777378896457 4187267342722333034172343)
                      ·
                        rfl

theorem cell23_8154674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2].length) (baseStart_8154674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8154674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8154674 prefixEnd_8154674 := by exact prefixLift 8154674
  have htrace : WordTrace (prefixWord ++ tailWord_8154674) baseStart_8154674 baseEnd_8154674 := by
    simpa [prefixWord, tailWord_8154674, baseEnd_8154674] using wordTrace_append hprefix tailTrace_8154674
  have hstable : (prefixWord ++ tailWord_8154674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8154674).length < 2 ^ (prefixWord ++ tailWord_8154674).sum := by decide
  have hdescent : baseEnd_8154674 < baseStart_8154674 := by decide
  rcases family_descends (prefixWord ++ tailWord_8154674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8154680 : List Nat := [2, 1, 2, 1, 4, 2, 1, 1, 9]
def baseStart_8154680 : Nat := 118140960795 + 8154680 * 2 ^ 59
def prefixEnd_8154680 : Nat := 4983230072969 + 3 ^ 40 * 8154680 * 2
def baseEnd_8154680 : Nat := 465252269289584445633035

theorem tailTrace_8154680 : CollatzResearch.WordTrace tailWord_8154680 prefixEnd_8154680 465252269289584445633035 := by
  unfold tailWord_8154680
  simp only [CollatzResearch.WordTrace]
  refine ⟨148712807048497271654962747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198283742731329695539950329 148712807048497271654962747)
  ·
    refine ⟨223069210572745907482444121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148712807048497271654962747 223069210572745907482444121)
    ·
      refine ⟨167301907929559430611833091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223069210572745907482444121 167301907929559430611833091)
      ·
        refine ⟨250952861894339145917749637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167301907929559430611833091 250952861894339145917749637)
        ·
          refine ⟨47053661605188589859578057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 250952861894339145917749637 47053661605188589859578057)
          ·
            refine ⟨35290246203891442394683543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47053661605188589859578057 35290246203891442394683543)
            ·
              refine ⟨52935369305837163592025315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35290246203891442394683543 52935369305837163592025315)
              ·
                refine ⟨79403053958755745388037973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52935369305837163592025315 79403053958755745388037973)
                ·
                  refine ⟨465252269289584445633035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 79403053958755745388037973 465252269289584445633035)
                  ·
                    rfl

theorem cell23_8154680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 9].length) (baseStart_8154680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8154680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8154680 prefixEnd_8154680 := by exact prefixLift 8154680
  have htrace : WordTrace (prefixWord ++ tailWord_8154680) baseStart_8154680 baseEnd_8154680 := by
    simpa [prefixWord, tailWord_8154680, baseEnd_8154680] using wordTrace_append hprefix tailTrace_8154680
  have hstable : (prefixWord ++ tailWord_8154680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8154680).length < 2 ^ (prefixWord ++ tailWord_8154680).sum := by decide
  have hdescent : baseEnd_8154680 < baseStart_8154680 := by decide
  rcases family_descends (prefixWord ++ tailWord_8154680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8154695 : List Nat := [1, 1, 4, 1, 6, 1, 2, 1, 1, 3, 2]
def baseStart_8154695 : Nat := 118140960795 + 8154695 * 2 ^ 59
def prefixEnd_8154695 : Nat := 4983230072969 + 3 ^ 40 * 8154695 * 2
def baseEnd_8154695 : Nat := 4187278125816077452009747

theorem tailTrace_8154695 : CollatzResearch.WordTrace tailWord_8154695 prefixEnd_8154695 4187278125816077452009747 := by
  unfold tailWord_8154695
  simp only [CollatzResearch.WordTrace]
  refine ⟨297426161191940200871721539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198284107461293467247814359 297426161191940200871721539)
  ·
    refine ⟨446139241787910301307582309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297426161191940200871721539 446139241787910301307582309)
    ·
      refine ⟨83651107835233181495171683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 446139241787910301307582309 83651107835233181495171683)
      ·
        refine ⟨125476661752849772242757525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83651107835233181495171683 125476661752849772242757525)
        ·
          refine ⟨5881718519664833073879259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 125476661752849772242757525 5881718519664833073879259)
          ·
            refine ⟨8822577779497249610818889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5881718519664833073879259 8822577779497249610818889)
            ·
              refine ⟨6616933334622937208114167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8822577779497249610818889 6616933334622937208114167)
              ·
                refine ⟨9925400001934405812171251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6616933334622937208114167 9925400001934405812171251)
                ·
                  refine ⟨14888100002901608718256877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9925400001934405812171251 14888100002901608718256877)
                  ·
                    refine ⟨5583037501088103269346329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14888100002901608718256877 5583037501088103269346329)
                    ·
                      refine ⟨4187278125816077452009747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5583037501088103269346329 4187278125816077452009747)
                      ·
                        rfl

theorem cell23_8154695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 1, 1, 3, 2].length) (baseStart_8154695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8154695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8154695 prefixEnd_8154695 := by exact prefixLift 8154695
  have htrace : WordTrace (prefixWord ++ tailWord_8154695) baseStart_8154695 baseEnd_8154695 := by
    simpa [prefixWord, tailWord_8154695, baseEnd_8154695] using wordTrace_append hprefix tailTrace_8154695
  have hstable : (prefixWord ++ tailWord_8154695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8154695).length < 2 ^ (prefixWord ++ tailWord_8154695).sum := by decide
  have hdescent : baseEnd_8154695 < baseStart_8154695 := by decide
  rcases family_descends (prefixWord ++ tailWord_8154695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8154720 : List Nat := [2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 7]
def baseStart_8154720 : Nat := 118140960795 + 8154720 * 2 ^ 59
def prefixEnd_8154720 : Nat := 4983230072969 + 3 ^ 40 * 8154720 * 2
def baseEnd_8154720 : Nat := 4187290962832439854197131

theorem tailTrace_8154720 : CollatzResearch.WordTrace tailWord_8154720 prefixEnd_8154720 4187290962832439854197131 := by
  unfold tailWord_8154720
  simp only [CollatzResearch.WordTrace]
  refine ⟨148713536508424815070690807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198284715344566420094254409 148713536508424815070690807)
  ·
    refine ⟨223070304762637222606036211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148713536508424815070690807 223070304762637222606036211)
    ·
      refine ⟨334605457143955833909054317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223070304762637222606036211 334605457143955833909054317)
      ·
        refine ⟨125477046428983437715895369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334605457143955833909054317 125477046428983437715895369)
        ·
          refine ⟨94107784821737578286921527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125477046428983437715895369 94107784821737578286921527)
          ·
            refine ⟨141161677232606367430382291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94107784821737578286921527 141161677232606367430382291)
            ·
              refine ⟨211742515848909551145573437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141161677232606367430382291 211742515848909551145573437)
              ·
                refine ⟨79403443443341081679590039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211742515848909551145573437 79403443443341081679590039)
                ·
                  refine ⟨119105165165011622519385059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79403443443341081679590039 119105165165011622519385059)
                  ·
                    refine ⟨178657747747517433779077589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 119105165165011622519385059 178657747747517433779077589)
                    ·
                      refine ⟨4187290962832439854197131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 178657747747517433779077589 4187290962832439854197131)
                      ·
                        rfl

theorem cell23_8154720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_8154720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8154720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8154720 prefixEnd_8154720 := by exact prefixLift 8154720
  have htrace : WordTrace (prefixWord ++ tailWord_8154720) baseStart_8154720 baseEnd_8154720 := by
    simpa [prefixWord, tailWord_8154720, baseEnd_8154720] using wordTrace_append hprefix tailTrace_8154720
  have hstable : (prefixWord ++ tailWord_8154720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8154720).length < 2 ^ (prefixWord ++ tailWord_8154720).sum := by decide
  have hdescent : baseEnd_8154720 < baseStart_8154720 := by decide
  rcases family_descends (prefixWord ++ tailWord_8154720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8154747 : List Nat := [1, 1, 1, 1, 1, 4, 4, 3, 2, 1, 4]
def baseStart_8154747 : Nat := 118140960795 + 8154747 * 2 ^ 59
def prefixEnd_8154747 : Nat := 4983230072969 + 3 ^ 40 * 8154747 * 2
def baseEnd_8154747 : Nat := 4187304826810111248559507

theorem tailTrace_8154747 : CollatzResearch.WordTrace tailWord_8154747 prefixEnd_8154747 4187304826810111248559507 := by
  unfold tailWord_8154747
  simp only [CollatzResearch.WordTrace]
  refine ⟨297428057787751813752614495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198285371858501209168409663 297428057787751813752614495)
  ·
    refine ⟨446142086681627720628921743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297428057787751813752614495 446142086681627720628921743)
    ·
      refine ⟨669213130022441580943382615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446142086681627720628921743 669213130022441580943382615)
      ·
        refine ⟨1003819695033662371415073923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 669213130022441580943382615 1003819695033662371415073923)
        ·
          refine ⟨1505729542550493557122610885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1003819695033662371415073923 1505729542550493557122610885)
          ·
            refine ⟨282324289228217541960489541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1505729542550493557122610885 282324289228217541960489541)
            ·
              refine ⟨52935804230290789117591789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 282324289228217541960489541 52935804230290789117591789)
              ·
                refine ⟨19850926586359045919096921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52935804230290789117591789 19850926586359045919096921)
                ·
                  refine ⟨14888194939769284439322691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19850926586359045919096921 14888194939769284439322691)
                  ·
                    refine ⟨22332292409653926658984037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14888194939769284439322691 22332292409653926658984037)
                    ·
                      refine ⟨4187304826810111248559507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22332292409653926658984037 4187304826810111248559507)
                      ·
                        rfl

theorem cell23_8154747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 2, 1, 4].length) (baseStart_8154747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8154747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8154747 prefixEnd_8154747 := by exact prefixLift 8154747
  have htrace : WordTrace (prefixWord ++ tailWord_8154747) baseStart_8154747 baseEnd_8154747 := by
    simpa [prefixWord, tailWord_8154747, baseEnd_8154747] using wordTrace_append hprefix tailTrace_8154747
  have hstable : (prefixWord ++ tailWord_8154747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8154747).length < 2 ^ (prefixWord ++ tailWord_8154747).sum := by decide
  have hdescent : baseEnd_8154747 < baseStart_8154747 := by decide
  rcases family_descends (prefixWord ++ tailWord_8154747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8154787 : List Nat := [1, 1, 1, 4, 1, 1, 5, 3, 6]
def baseStart_8154787 : Nat := 118140960795 + 8154787 * 2 ^ 59
def prefixEnd_8154787 : Nat := 4983230072969 + 3 ^ 40 * 8154787 * 2
def baseEnd_8154787 : Nat := 465258374004032343562147

theorem tailTrace_8154787 : CollatzResearch.WordTrace tailWord_8154787 prefixEnd_8154787 465258374004032343562147 := by
  unfold tailWord_8154787
  simp only [CollatzResearch.WordTrace]
  refine ⟨297429516707606900584070615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198286344471737933722713743 297429516707606900584070615)
  ·
    refine ⟨446144275061410350876105923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297429516707606900584070615 446144275061410350876105923)
    ·
      refine ⟨669216412592115526314158885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446144275061410350876105923 669216412592115526314158885)
      ·
        refine ⟨125478077361021661183904791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 669216412592115526314158885 125478077361021661183904791)
        ·
          refine ⟨188217116041532491775857187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125478077361021661183904791 188217116041532491775857187)
          ·
            refine ⟨282325674062298737663785781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188217116041532491775857187 282325674062298737663785781)
            ·
              refine ⟨26468031943340506655979917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 282325674062298737663785781 26468031943340506655979917)
              ·
                refine ⟨9925511978752689995992469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26468031943340506655979917 9925511978752689995992469)
                ·
                  refine ⟨465258374004032343562147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9925511978752689995992469 465258374004032343562147)
                  ·
                    rfl

theorem cell23_8154787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 3, 6].length) (baseStart_8154787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8154787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8154787 prefixEnd_8154787 := by exact prefixLift 8154787
  have htrace : WordTrace (prefixWord ++ tailWord_8154787) baseStart_8154787 baseEnd_8154787 := by
    simpa [prefixWord, tailWord_8154787, baseEnd_8154787] using wordTrace_append hprefix tailTrace_8154787
  have hstable : (prefixWord ++ tailWord_8154787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8154787).length < 2 ^ (prefixWord ++ tailWord_8154787).sum := by decide
  have hdescent : baseEnd_8154787 < baseStart_8154787 := by decide
  rcases family_descends (prefixWord ++ tailWord_8154787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8154798 : List Nat := [4, 1, 4, 1, 2, 1, 2, 1, 2, 1, 4]
def baseStart_8154798 : Nat := 118140960795 + 8154798 * 2 ^ 59
def prefixEnd_8154798 : Nat := 4983230072969 + 3 ^ 40 * 8154798 * 2
def baseEnd_8154798 : Nat := 4187331014323490549021773

theorem tailTrace_8154798 : CollatzResearch.WordTrace tailWord_8154798 prefixEnd_8154798 4187331014323490549021773 := by
  unfold tailWord_8154798
  simp only [CollatzResearch.WordTrace]
  refine ⟨37178739738820881182840131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198286611940378032975147365 37178739738820881182840131)
  ·
    refine ⟨55768109608231321774260197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37178739738820881182840131 55768109608231321774260197)
    ·
      refine ⟨10456520551543372832673787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55768109608231321774260197 10456520551543372832673787)
      ·
        refine ⟨15684780827315059249010681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10456520551543372832673787 15684780827315059249010681)
        ·
          refine ⟨11763585620486294436758011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15684780827315059249010681 11763585620486294436758011)
          ·
            refine ⟨17645378430729441655137017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11763585620486294436758011 17645378430729441655137017)
            ·
              refine ⟨13234033823047081241352763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17645378430729441655137017 13234033823047081241352763)
              ·
                refine ⟨19851050734570621862029145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13234033823047081241352763 19851050734570621862029145)
                ·
                  refine ⟨14888288050927966396521859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19851050734570621862029145 14888288050927966396521859)
                  ·
                    refine ⟨22332432076391949594782789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14888288050927966396521859 22332432076391949594782789)
                    ·
                      refine ⟨4187331014323490549021773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22332432076391949594782789 4187331014323490549021773)
                      ·
                        rfl

theorem cell23_8154798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_8154798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8154798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8154798 prefixEnd_8154798 := by exact prefixLift 8154798
  have htrace : WordTrace (prefixWord ++ tailWord_8154798) baseStart_8154798 baseEnd_8154798 := by
    simpa [prefixWord, tailWord_8154798, baseEnd_8154798] using wordTrace_append hprefix tailTrace_8154798
  have hstable : (prefixWord ++ tailWord_8154798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8154798).length < 2 ^ (prefixWord ++ tailWord_8154798).sum := by decide
  have hdescent : baseEnd_8154798 < baseStart_8154798 := by decide
  rcases family_descends (prefixWord ++ tailWord_8154798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8154834 : List Nat := [3, 2, 2, 2, 2, 1, 1, 2, 3, 5]
def baseStart_8154834 : Nat := 118140960795 + 8154834 * 2 ^ 59
def prefixEnd_8154834 : Nat := 4983230072969 + 3 ^ 40 * 8154834 * 2
def baseEnd_8154834 : Nat := 1395783166542350802723869

theorem tailTrace_8154834 : CollatzResearch.WordTrace tailWord_8154834 prefixEnd_8154834 1395783166542350802723869 := by
  unfold tailWord_8154834
  simp only [CollatzResearch.WordTrace]
  refine ⟨74357807734609156902757889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198287487292291085074021037 74357807734609156902757889)
  ·
    refine ⟨55768355800956867677068417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74357807734609156902757889 55768355800956867677068417)
    ·
      refine ⟨41826266850717650757801313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55768355800956867677068417 41826266850717650757801313)
      ·
        refine ⟨31369700138038238068350985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41826266850717650757801313 31369700138038238068350985)
        ·
          refine ⟨23527275103528678551263239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31369700138038238068350985 23527275103528678551263239)
          ·
            refine ⟨35290912655293017826894859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23527275103528678551263239 35290912655293017826894859)
            ·
              refine ⟨52936368982939526740342289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35290912655293017826894859 52936368982939526740342289)
              ·
                refine ⟨39702276737204645055256717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52936368982939526740342289 39702276737204645055256717)
                ·
                  refine ⟨14888353776451741895721269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39702276737204645055256717 14888353776451741895721269)
                  ·
                    refine ⟨1395783166542350802723869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14888353776451741895721269 1395783166542350802723869)
                    ·
                      rfl

theorem cell23_8154834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_8154834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8154834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8154834 prefixEnd_8154834 := by exact prefixLift 8154834
  have htrace : WordTrace (prefixWord ++ tailWord_8154834) baseStart_8154834 baseEnd_8154834 := by
    simpa [prefixWord, tailWord_8154834, baseEnd_8154834] using wordTrace_append hprefix tailTrace_8154834
  have hstable : (prefixWord ++ tailWord_8154834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8154834).length < 2 ^ (prefixWord ++ tailWord_8154834).sum := by decide
  have hdescent : baseEnd_8154834 < baseStart_8154834 := by decide
  rcases family_descends (prefixWord ++ tailWord_8154834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8154871 : List Nat := [1, 1, 3, 1, 1, 1, 8, 1, 1, 1, 4]
def baseStart_8154871 : Nat := 118140960795 + 8154871 * 2 ^ 59
def prefixEnd_8154871 : Nat := 4983230072969 + 3 ^ 40 * 8154871 * 2
def baseEnd_8154871 : Nat := 4187368498411268763408937

theorem tailTrace_8154871 : CollatzResearch.WordTrace tailWord_8154871 prefixEnd_8154871 4187368498411268763408937 := by
  unfold tailWord_8154871
  simp only [CollatzResearch.WordTrace]
  refine ⟨297432580439302582930128467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198288386959535055286752311 297432580439302582930128467)
  ·
    refine ⟨446148870658953874395192701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297432580439302582930128467 446148870658953874395192701)
    ·
      refine ⟨167305826497107702898197263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 446148870658953874395192701 167305826497107702898197263)
      ·
        refine ⟨250958739745661554347295895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167305826497107702898197263 250958739745661554347295895)
        ·
          refine ⟨376438109618492331520943843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250958739745661554347295895 376438109618492331520943843)
          ·
            refine ⟨564657164427738497281415765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376438109618492331520943843 564657164427738497281415765)
            ·
              refine ⟨6617076145637560515016591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 564657164427738497281415765 6617076145637560515016591)
              ·
                refine ⟨9925614218456340772524887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6617076145637560515016591 9925614218456340772524887)
                ·
                  refine ⟨14888421327684511158787331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9925614218456340772524887 14888421327684511158787331)
                  ·
                    refine ⟨22332631991526766738180997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14888421327684511158787331 22332631991526766738180997)
                    ·
                      refine ⟨4187368498411268763408937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22332631991526766738180997 4187368498411268763408937)
                      ·
                        rfl

theorem cell23_8154871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 1, 1, 1, 4].length) (baseStart_8154871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8154871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8154871 prefixEnd_8154871 := by exact prefixLift 8154871
  have htrace : WordTrace (prefixWord ++ tailWord_8154871) baseStart_8154871 baseEnd_8154871 := by
    simpa [prefixWord, tailWord_8154871, baseEnd_8154871] using wordTrace_append hprefix tailTrace_8154871
  have hstable : (prefixWord ++ tailWord_8154871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8154871).length < 2 ^ (prefixWord ++ tailWord_8154871).sum := by decide
  have hdescent : baseEnd_8154871 < baseStart_8154871 := by decide
  rcases family_descends (prefixWord ++ tailWord_8154871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8154881 : List Nat := [1, 2, 4, 1, 1, 1, 5, 2, 2, 4]
def baseStart_8154881 : Nat := 118140960795 + 8154881 * 2 ^ 59
def prefixEnd_8154881 : Nat := 4983230072969 + 3 ^ 40 * 8154881 * 2
def baseEnd_8154881 : Nat := 1395791211072604574761297

theorem tailTrace_8154881 : CollatzResearch.WordTrace tailWord_8154881 prefixEnd_8154881 1395791211072604574761297 := by
  unfold tailWord_8154881
  simp only [CollatzResearch.WordTrace]
  refine ⟨297432945169266354637992497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198288630112844236425328331 297432945169266354637992497)
  ·
    refine ⟨223074708876949765978494373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297432945169266354637992497 223074708876949765978494373)
    ·
      refine ⟨41826507914428081120967695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223074708876949765978494373 41826507914428081120967695)
      ·
        refine ⟨62739761871642121681451543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41826507914428081120967695 62739761871642121681451543)
        ·
          refine ⟨94109642807463182522177315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62739761871642121681451543 94109642807463182522177315)
          ·
            refine ⟨141164464211194773783265973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94109642807463182522177315 141164464211194773783265973)
            ·
              refine ⟨13234168519799510042181185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141164464211194773783265973 13234168519799510042181185)
              ·
                refine ⟨9925626389849632531635889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13234168519799510042181185 9925626389849632531635889)
                ·
                  refine ⟨7444219792387224398726917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9925626389849632531635889 7444219792387224398726917)
                  ·
                    refine ⟨1395791211072604574761297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7444219792387224398726917 1395791211072604574761297)
                    ·
                      rfl

theorem cell23_8154881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_8154881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8154881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8154881 prefixEnd_8154881 := by exact prefixLift 8154881
  have htrace : WordTrace (prefixWord ++ tailWord_8154881) baseStart_8154881 baseEnd_8154881 := by
    simpa [prefixWord, tailWord_8154881, baseEnd_8154881] using wordTrace_append hprefix tailTrace_8154881
  have hstable : (prefixWord ++ tailWord_8154881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8154881).length < 2 ^ (prefixWord ++ tailWord_8154881).sum := by decide
  have hdescent : baseEnd_8154881 < baseStart_8154881 := by decide
  rcases family_descends (prefixWord ++ tailWord_8154881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8154888 : List Nat := [2, 1, 3, 2, 2, 1, 4, 1, 3, 2, 2]
def baseStart_8154888 : Nat := 118140960795 + 8154888 * 2 ^ 59
def prefixEnd_8154888 : Nat := 4983230072969 + 3 ^ 40 * 8154888 * 2
def baseEnd_8154888 : Nat := 4187377227582395196896359

theorem tailTrace_8154888 : CollatzResearch.WordTrace tailWord_8154888 prefixEnd_8154888 4187377227582395196896359 := by
  unfold tailWord_8154888
  simp only [CollatzResearch.WordTrace]
  refine ⟨148716600240120497416748659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198288800320160663222331545 148716600240120497416748659)
  ·
    refine ⟨223074900360180746125122989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148716600240120497416748659 223074900360180746125122989)
    ·
      refine ⟨83653087635067779796921121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223074900360180746125122989 83653087635067779796921121)
      ·
        refine ⟨62739815726300834847690841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83653087635067779796921121 62739815726300834847690841)
        ·
          refine ⟨47054861794725626135768131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62739815726300834847690841 47054861794725626135768131)
          ·
            refine ⟨70582292692088439203652197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47054861794725626135768131 70582292692088439203652197)
            ·
              refine ⟨13234179879766582350684787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70582292692088439203652197 13234179879766582350684787)
              ·
                refine ⟨19851269819649873526027181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13234179879766582350684787 19851269819649873526027181)
                ·
                  refine ⟨7444226182368702572260193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19851269819649873526027181 7444226182368702572260193)
                  ·
                    refine ⟨5583169636776526929195145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7444226182368702572260193 5583169636776526929195145)
                    ·
                      refine ⟨4187377227582395196896359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5583169636776526929195145 4187377227582395196896359)
                      ·
                        rfl

theorem cell23_8154888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 3, 2, 2].length) (baseStart_8154888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8154888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8154888 prefixEnd_8154888 := by exact prefixLift 8154888
  have htrace : WordTrace (prefixWord ++ tailWord_8154888) baseStart_8154888 baseEnd_8154888 := by
    simpa [prefixWord, tailWord_8154888, baseEnd_8154888] using wordTrace_append hprefix tailTrace_8154888
  have hstable : (prefixWord ++ tailWord_8154888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8154888).length < 2 ^ (prefixWord ++ tailWord_8154888).sum := by decide
  have hdescent : baseEnd_8154888 < baseStart_8154888 := by decide
  rcases family_descends (prefixWord ++ tailWord_8154888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8154898 : List Nat := [3, 2, 4, 1, 1, 3, 1, 1, 1, 6]
def baseStart_8154898 : Nat := 118140960795 + 8154898 * 2 ^ 59
def prefixEnd_8154898 : Nat := 4983230072969 + 3 ^ 40 * 8154898 * 2
def baseEnd_8154898 : Nat := 1395794120796313385923771

theorem tailTrace_8154898 : CollatzResearch.WordTrace tailWord_8154898 prefixEnd_8154898 1395794120796313385923771 := by
  unfold tailWord_8154898
  simp only [CollatzResearch.WordTrace]
  refine ⟨74358391302551191635340337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198289043473469844360907565 74358391302551191635340337)
  ·
    refine ⟨55768793476913393726505253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74358391302551191635340337 55768793476913393726505253)
    ·
      refine ⟨10456648776921261323719735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55768793476913393726505253 10456648776921261323719735)
      ·
        refine ⟨15684973165381891985579603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10456648776921261323719735 15684973165381891985579603)
        ·
          refine ⟨23527459748072837978369405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15684973165381891985579603 23527459748072837978369405)
          ·
            refine ⟨8822797405527314241888527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23527459748072837978369405 8822797405527314241888527)
            ·
              refine ⟨13234196108290971362832791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8822797405527314241888527 13234196108290971362832791)
              ·
                refine ⟨19851294162436457044249187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13234196108290971362832791 19851294162436457044249187)
                ·
                  refine ⟨29776941243654685566373781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19851294162436457044249187 29776941243654685566373781)
                  ·
                    refine ⟨1395794120796313385923771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29776941243654685566373781 1395794120796313385923771)
                    ·
                      rfl

theorem cell23_8154898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_8154898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8154898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8154898 prefixEnd_8154898 := by exact prefixLift 8154898
  have htrace : WordTrace (prefixWord ++ tailWord_8154898) baseStart_8154898 baseEnd_8154898 := by
    simpa [prefixWord, tailWord_8154898, baseEnd_8154898] using wordTrace_append hprefix tailTrace_8154898
  have hstable : (prefixWord ++ tailWord_8154898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8154898).length < 2 ^ (prefixWord ++ tailWord_8154898).sum := by decide
  have hdescent : baseEnd_8154898 < baseStart_8154898 := by decide
  rcases family_descends (prefixWord ++ tailWord_8154898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8154901 : List Nat := [1, 3, 2, 1, 2, 5, 1, 1, 1, 2, 4]
def baseStart_8154901 : Nat := 118140960795 + 8154901 * 2 ^ 59
def prefixEnd_8154901 : Nat := 4983230072969 + 3 ^ 40 * 8154901 * 2
def baseEnd_8154901 : Nat := 4187383902830903646033799

theorem tailTrace_8154901 : CollatzResearch.WordTrace tailWord_8154901 prefixEnd_8154901 4187383902830903646033799 := by
  unfold tailWord_8154901
  simp only [CollatzResearch.WordTrace]
  refine ⟨297433674629193898053720557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198289116419462598702480371 297433674629193898053720557)
  ·
    refine ⟨111537627985947711770145209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297433674629193898053720557 111537627985947711770145209)
    ·
      refine ⟨83653220989460783827608907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111537627985947711770145209 83653220989460783827608907)
      ·
        refine ⟨125479831484191175741413361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83653220989460783827608907 125479831484191175741413361)
        ·
          refine ⟨94109873613143381806060021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125479831484191175741413361 94109873613143381806060021)
          ·
            refine ⟨8822800651232192044318127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94109873613143381806060021 8822800651232192044318127)
            ·
              refine ⟨13234200976848288066477191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8822800651232192044318127 13234200976848288066477191)
              ·
                refine ⟨19851301465272432099715787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13234200976848288066477191 19851301465272432099715787)
                ·
                  refine ⟨29776952197908648149573681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19851301465272432099715787 29776952197908648149573681)
                  ·
                    refine ⟨22332714148431486112180261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29776952197908648149573681 22332714148431486112180261)
                    ·
                      refine ⟨4187383902830903646033799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22332714148431486112180261 4187383902830903646033799)
                      ·
                        rfl

theorem cell23_8154901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 2, 4].length) (baseStart_8154901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8154901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8154901 prefixEnd_8154901 := by exact prefixLift 8154901
  have htrace : WordTrace (prefixWord ++ tailWord_8154901) baseStart_8154901 baseEnd_8154901 := by
    simpa [prefixWord, tailWord_8154901, baseEnd_8154901] using wordTrace_append hprefix tailTrace_8154901
  have hstable : (prefixWord ++ tailWord_8154901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8154901).length < 2 ^ (prefixWord ++ tailWord_8154901).sum := by decide
  have hdescent : baseEnd_8154901 < baseStart_8154901 := by decide
  rcases family_descends (prefixWord ++ tailWord_8154901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8154965 : List Nat := [1, 3, 2, 2, 2, 4, 1, 2, 1, 3, 2]
def baseStart_8154965 : Nat := 118140960795 + 8154965 * 2 ^ 59
def prefixEnd_8154965 : Nat := 4983230072969 + 3 ^ 40 * 8154965 * 2
def baseEnd_8154965 : Nat := 4187416765592791395633505

theorem tailTrace_8154965 : CollatzResearch.WordTrace tailWord_8154965 prefixEnd_8154965 4187416765592791395633505 := by
  unfold tailWord_8154965
  simp only [CollatzResearch.WordTrace]
  refine ⟨297436008900962036984050349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198290672600641357989366899 297436008900962036984050349)
  ·
    refine ⟨111538503337860763869018881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297436008900962036984050349 111538503337860763869018881)
    ·
      refine ⟨83653877503395572901764161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111538503337860763869018881 83653877503395572901764161)
      ·
        refine ⟨62740408127546679676323121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83653877503395572901764161 62740408127546679676323121)
        ·
          refine ⟨47055306095660009757242341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62740408127546679676323121 47055306095660009757242341)
          ·
            refine ⟨8822869892936251829482939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47055306095660009757242341 8822869892936251829482939)
            ·
              refine ⟨13234304839404377744224409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8822869892936251829482939 13234304839404377744224409)
              ·
                refine ⟨9925728629553283308168307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13234304839404377744224409 9925728629553283308168307)
                ·
                  refine ⟨14888592944329924962252461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9925728629553283308168307 14888592944329924962252461)
                  ·
                    refine ⟨5583222354123721860844673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14888592944329924962252461 5583222354123721860844673)
                    ·
                      refine ⟨4187416765592791395633505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5583222354123721860844673 4187416765592791395633505)
                      ·
                        rfl

theorem cell23_8154965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 2, 1, 3, 2].length) (baseStart_8154965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8154965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8154965 prefixEnd_8154965 := by exact prefixLift 8154965
  have htrace : WordTrace (prefixWord ++ tailWord_8154965) baseStart_8154965 baseEnd_8154965 := by
    simpa [prefixWord, tailWord_8154965, baseEnd_8154965] using wordTrace_append hprefix tailTrace_8154965
  have hstable : (prefixWord ++ tailWord_8154965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8154965).length < 2 ^ (prefixWord ++ tailWord_8154965).sum := by decide
  have hdescent : baseEnd_8154965 < baseStart_8154965 := by decide
  rcases family_descends (prefixWord ++ tailWord_8154965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8154978 : List Nat := [3, 3, 2, 1, 2, 1, 1, 1, 3, 4, 2]
def baseStart_8154978 : Nat := 118140960795 + 8154978 * 2 ^ 59
def prefixEnd_8154978 : Nat := 4983230072969 + 3 ^ 40 * 8154978 * 2
def baseEnd_8154978 : Nat := 4187423440841299844770945

theorem tailTrace_8154978 : CollatzResearch.WordTrace tailWord_8154978 prefixEnd_8154978 4187423440841299844770945 := by
  unfold tailWord_8154978
  simp only [CollatzResearch.WordTrace]
  refine ⟨74359120762478735051068397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198290988699943293469515725 74359120762478735051068397)
  ·
    refine ⟨27884670285929525644150649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74359120762478735051068397 27884670285929525644150649)
    ·
      refine ⟨20913502714447144233112987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27884670285929525644150649 20913502714447144233112987)
      ·
        refine ⟨31370254071670716349669481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20913502714447144233112987 31370254071670716349669481)
        ·
          refine ⟨23527690553753037262252111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31370254071670716349669481 23527690553753037262252111)
          ·
            refine ⟨35291535830629555893378167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23527690553753037262252111 35291535830629555893378167)
            ·
              refine ⟨52937303745944333840067251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35291535830629555893378167 52937303745944333840067251)
              ·
                refine ⟨79405955618916500760100877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52937303745944333840067251 79405955618916500760100877)
                ·
                  refine ⟨29777233357093687785037829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79405955618916500760100877 29777233357093687785037829)
                  ·
                    refine ⟨5583231254455066459694593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29777233357093687785037829 5583231254455066459694593)
                    ·
                      refine ⟨4187423440841299844770945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5583231254455066459694593 4187423440841299844770945)
                      ·
                        rfl

theorem cell23_8154978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_8154978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8154978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8154978 prefixEnd_8154978 := by exact prefixLift 8154978
  have htrace : WordTrace (prefixWord ++ tailWord_8154978) baseStart_8154978 baseEnd_8154978 := by
    simpa [prefixWord, tailWord_8154978, baseEnd_8154978] using wordTrace_append hprefix tailTrace_8154978
  have hstable : (prefixWord ++ tailWord_8154978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8154978).length < 2 ^ (prefixWord ++ tailWord_8154978).sum := by decide
  have hdescent : baseEnd_8154978 < baseStart_8154978 := by decide
  rcases family_descends (prefixWord ++ tailWord_8154978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8155001 : List Nat := [1, 2, 1, 3, 2, 2, 3, 4, 5]
def baseStart_8155001 : Nat := 118140960795 + 8155001 * 2 ^ 59
def prefixEnd_8155001 : Nat := 4983230072969 + 3 ^ 40 * 8155001 * 2
def baseEnd_8155001 : Nat := 465270583432928139420371

theorem tailTrace_8155001 : CollatzResearch.WordTrace tailWord_8155001 prefixEnd_8155001 465270583432928139420371 := by
  unfold tailWord_8155001
  simp only [CollatzResearch.WordTrace]
  refine ⟨297437321928831615132360857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198291547952554410088240571 297437321928831615132360857)
  ·
    refine ⟨223077991446623711349270643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297437321928831615132360857 223077991446623711349270643)
    ·
      refine ⟨334616987169935567023905965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223077991446623711349270643 334616987169935567023905965)
      ·
        refine ⟨125481370188725837633964737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334616987169935567023905965 125481370188725837633964737)
        ·
          refine ⟨94111027641544378225473553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125481370188725837633964737 94111027641544378225473553)
          ·
            refine ⟨70583270731158283669105165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94111027641544378225473553 70583270731158283669105165)
            ·
              refine ⟨26468726524184356375914437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70583270731158283669105165 26468726524184356375914437)
              ·
                refine ⟨4962886223284566820483957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26468726524184356375914437 4962886223284566820483957)
                ·
                  refine ⟨465270583432928139420371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4962886223284566820483957 465270583432928139420371)
                  ·
                    rfl

theorem cell23_8155001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 4, 5].length) (baseStart_8155001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155001 prefixEnd_8155001 := by exact prefixLift 8155001
  have htrace : WordTrace (prefixWord ++ tailWord_8155001) baseStart_8155001 baseEnd_8155001 := by
    simpa [prefixWord, tailWord_8155001, baseEnd_8155001] using wordTrace_append hprefix tailTrace_8155001
  have hstable : (prefixWord ++ tailWord_8155001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155001).length < 2 ^ (prefixWord ++ tailWord_8155001).sum := by decide
  have hdescent : baseEnd_8155001 < baseStart_8155001 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8155011 : List Nat := [1, 1, 1, 3, 4, 3, 1, 1, 2, 3, 3]
def baseStart_8155011 : Nat := 118140960795 + 8155011 * 2 ^ 59
def prefixEnd_8155011 : Nat := 4983230072969 + 3 ^ 40 * 8155011 * 2
def baseEnd_8155011 : Nat := 4187440385702898215658293

theorem tailTrace_8155011 : CollatzResearch.WordTrace tailWord_8155011 prefixEnd_8155011 4187440385702898215658293 := by
  unfold tailWord_8155011
  simp only [CollatzResearch.WordTrace]
  refine ⟨297437686658795386840224887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198291791105863591226816591 297437686658795386840224887)
  ·
    refine ⟨446156529988193080260337331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297437686658795386840224887 446156529988193080260337331)
    ·
      refine ⟨669234794982289620390505997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446156529988193080260337331 669234794982289620390505997)
      ·
        refine ⟨250963048118358607646439749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 669234794982289620390505997 250963048118358607646439749)
        ·
          refine ⟨47055571522192238933707453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 250963048118358607646439749 47055571522192238933707453)
          ·
            refine ⟨17645839320822089600140295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47055571522192238933707453 17645839320822089600140295)
            ·
              refine ⟨26468758981233134400210443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17645839320822089600140295 26468758981233134400210443)
              ·
                refine ⟨39703138471849701600315665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26468758981233134400210443 39703138471849701600315665)
                ·
                  refine ⟨29777353853887276200236749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39703138471849701600315665 29777353853887276200236749)
                  ·
                    refine ⟨11166507695207728575088781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29777353853887276200236749 11166507695207728575088781)
                    ·
                      refine ⟨4187440385702898215658293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11166507695207728575088781 4187440385702898215658293)
                      ·
                        rfl

theorem cell23_8155011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 3, 3].length) (baseStart_8155011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155011 prefixEnd_8155011 := by exact prefixLift 8155011
  have htrace : WordTrace (prefixWord ++ tailWord_8155011) baseStart_8155011 baseEnd_8155011 := by
    simpa [prefixWord, tailWord_8155011, baseEnd_8155011] using wordTrace_append hprefix tailTrace_8155011
  have hstable : (prefixWord ++ tailWord_8155011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155011).length < 2 ^ (prefixWord ++ tailWord_8155011).sum := by decide
  have hdescent : baseEnd_8155011 < baseStart_8155011 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8155031 : List Nat := [1, 1, 3, 3, 1, 3, 3, 1, 2, 5]
def baseStart_8155031 : Nat := 118140960795 + 8155031 * 2 ^ 59
def prefixEnd_8155031 : Nat := 4983230072969 + 3 ^ 40 * 8155031 * 2
def baseEnd_8155031 : Nat := 1395816885105329379136067

theorem tailTrace_8155031 : CollatzResearch.WordTrace tailWord_8155031 prefixEnd_8155031 1395816885105329379136067 := by
  unfold tailWord_8155031
  simp only [CollatzResearch.WordTrace]
  refine ⟨297438416118722930255952947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198292277412481953503968631 297438416118722930255952947)
  ·
    refine ⟨446157624178084395383929421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297438416118722930255952947 446157624178084395383929421)
    ·
      refine ⟨167309109066781648268973533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 446157624178084395383929421 167309109066781648268973533)
      ·
        refine ⟨62740915900043118100865075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167309109066781648268973533 62740915900043118100865075)
        ·
          refine ⟨94111373850064677151297613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62740915900043118100865075 94111373850064677151297613)
          ·
            refine ⟨35291765193774253931736605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94111373850064677151297613 35291765193774253931736605)
            ·
              refine ⟨13234411947665345224401227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35291765193774253931736605 13234411947665345224401227)
              ·
                refine ⟨19851617921498017836601841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13234411947665345224401227 19851617921498017836601841)
                ·
                  refine ⟨14888713441123513377451381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19851617921498017836601841 14888713441123513377451381)
                  ·
                    refine ⟨1395816885105329379136067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14888713441123513377451381 1395816885105329379136067)
                    ·
                      rfl

theorem cell23_8155031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 2, 5].length) (baseStart_8155031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155031 prefixEnd_8155031 := by exact prefixLift 8155031
  have htrace : WordTrace (prefixWord ++ tailWord_8155031) baseStart_8155031 baseEnd_8155031 := by
    simpa [prefixWord, tailWord_8155031, baseEnd_8155031] using wordTrace_append hprefix tailTrace_8155031
  have hstable : (prefixWord ++ tailWord_8155031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155031).length < 2 ^ (prefixWord ++ tailWord_8155031).sum := by decide
  have hdescent : baseEnd_8155031 < baseStart_8155031 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8155064 : List Nat := [2, 1, 2, 1, 2, 3, 1, 2, 2, 1, 6]
def baseStart_8155064 : Nat := 118140960795 + 8155064 * 2 ^ 59
def prefixEnd_8155064 : Nat := 4983230072969 + 3 ^ 40 * 8155064 * 2
def baseEnd_8155064 : Nat := 4187467600177586508295549

theorem tailTrace_8155064 : CollatzResearch.WordTrace tailWord_8155064 prefixEnd_8155064 4187467600177586508295549 := by
  unfold tailWord_8155064
  simp only [CollatzResearch.WordTrace]
  refine ⟨148719809863801688445952123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198293079818402251261269497 148719809863801688445952123)
  ·
    refine ⟨223079714795702532668928185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148719809863801688445952123 223079714795702532668928185)
    ·
      refine ⟨167309786096776899501696139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223079714795702532668928185 167309786096776899501696139)
      ·
        refine ⟨250964679145165349252544209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167309786096776899501696139 250964679145165349252544209)
        ·
          refine ⟨188223509358874011939408157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250964679145165349252544209 188223509358874011939408157)
          ·
            refine ⟨70583816009577754477278059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188223509358874011939408157 70583816009577754477278059)
            ·
              refine ⟨105875724014366631715917089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70583816009577754477278059 105875724014366631715917089)
              ·
                refine ⟨79406793010774973786937817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105875724014366631715917089 79406793010774973786937817)
                ·
                  refine ⟨59555094758081230340203363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79406793010774973786937817 59555094758081230340203363)
                  ·
                    refine ⟨89332642137121845510305045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59555094758081230340203363 89332642137121845510305045)
                    ·
                      refine ⟨4187467600177586508295549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89332642137121845510305045 4187467600177586508295549)
                      ·
                        rfl

theorem cell23_8155064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 2, 1, 6].length) (baseStart_8155064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155064 prefixEnd_8155064 := by exact prefixLift 8155064
  have htrace : WordTrace (prefixWord ++ tailWord_8155064) baseStart_8155064 baseEnd_8155064 := by
    simpa [prefixWord, tailWord_8155064, baseEnd_8155064] using wordTrace_append hprefix tailTrace_8155064
  have hstable : (prefixWord ++ tailWord_8155064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155064).length < 2 ^ (prefixWord ++ tailWord_8155064).sum := by decide
  have hdescent : baseEnd_8155064 < baseStart_8155064 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8155171 : List Nat := [1, 1, 1, 4, 3, 1, 1, 2, 3, 2, 4]
def baseStart_8155171 : Nat := 118140960795 + 8155171 * 2 ^ 59
def prefixEnd_8155171 : Nat := 4983230072969 + 3 ^ 40 * 8155171 * 2
def baseEnd_8155171 : Nat := 4187522542607617589657557

theorem tailTrace_8155171 : CollatzResearch.WordTrace tailWord_8155171 prefixEnd_8155171 4187522542607617589657557 := by
  unfold tailWord_8155171
  simp only [CollatzResearch.WordTrace]
  refine ⟨297443522338215734166049367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198295681558810489444032911 297443522338215734166049367)
  ·
    refine ⟨446165283507323601249074051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297443522338215734166049367 446165283507323601249074051)
    ·
      refine ⟨669247925260985401873611077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446165283507323601249074051 669247925260985401873611077)
      ·
        refine ⟨125483985986434762851302077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 669247925260985401873611077 125483985986434762851302077)
        ·
          refine ⟨47056494744913036069238279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125483985986434762851302077 47056494744913036069238279)
          ·
            refine ⟨70584742117369554103857419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47056494744913036069238279 70584742117369554103857419)
            ·
              refine ⟨105877113176054331155786129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70584742117369554103857419 105877113176054331155786129)
              ·
                refine ⟨79407834882040748366839597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105877113176054331155786129 79407834882040748366839597)
                ·
                  refine ⟨29777938080765280637564849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79407834882040748366839597 29777938080765280637564849)
                  ·
                    refine ⟨22333453560573960478173637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29777938080765280637564849 22333453560573960478173637)
                    ·
                      refine ⟨4187522542607617589657557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22333453560573960478173637 4187522542607617589657557)
                      ·
                        rfl

theorem cell23_8155171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_8155171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155171 prefixEnd_8155171 := by exact prefixLift 8155171
  have htrace : WordTrace (prefixWord ++ tailWord_8155171) baseStart_8155171 baseEnd_8155171 := by
    simpa [prefixWord, tailWord_8155171, baseEnd_8155171] using wordTrace_append hprefix tailTrace_8155171
  have hstable : (prefixWord ++ tailWord_8155171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155171).length < 2 ^ (prefixWord ++ tailWord_8155171).sum := by decide
  have hdescent : baseEnd_8155171 < baseStart_8155171 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8155192 : List Nat := [2, 1, 2, 1, 6, 1, 1, 2, 3, 2, 2]
def baseStart_8155192 : Nat := 118140960795 + 8155192 * 2 ^ 59
def prefixEnd_8155192 : Nat := 4983230072969 + 3 ^ 40 * 8155192 * 2
def baseEnd_8155192 : Nat := 4187533325701362007494961

theorem tailTrace_8155192 : CollatzResearch.WordTrace tailWord_8155192 prefixEnd_8155192 4187533325701362007494961 := by
  unfold tailWord_8155192
  simp only [CollatzResearch.WordTrace]
  refine ⟨148722144135569827376281915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198296192180759769835042553 148722144135569827376281915)
  ·
    refine ⟨223083216203354741064422873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148722144135569827376281915 223083216203354741064422873)
    ·
      refine ⟨167312412152516055798317155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223083216203354741064422873 167312412152516055798317155)
      ·
        refine ⟨250968618228774083697475733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167312412152516055798317155 250968618228774083697475733)
        ·
          refine ⟨11764153979473785173319175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 250968618228774083697475733 11764153979473785173319175)
          ·
            refine ⟨17646230969210677759978763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11764153979473785173319175 17646230969210677759978763)
            ·
              refine ⟨26469346453816016639968145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17646230969210677759978763 26469346453816016639968145)
              ·
                refine ⟨19852009840362012479976109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26469346453816016639968145 19852009840362012479976109)
                ·
                  refine ⟨7444503690135754679991041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19852009840362012479976109 7444503690135754679991041)
                  ·
                    refine ⟨5583377767601816009993281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7444503690135754679991041 5583377767601816009993281)
                    ·
                      refine ⟨4187533325701362007494961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5583377767601816009993281 4187533325701362007494961)
                      ·
                        rfl

theorem cell23_8155192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 3, 2, 2].length) (baseStart_8155192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155192 prefixEnd_8155192 := by exact prefixLift 8155192
  have htrace : WordTrace (prefixWord ++ tailWord_8155192) baseStart_8155192 baseEnd_8155192 := by
    simpa [prefixWord, tailWord_8155192, baseEnd_8155192] using wordTrace_append hprefix tailTrace_8155192
  have hstable : (prefixWord ++ tailWord_8155192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155192).length < 2 ^ (prefixWord ++ tailWord_8155192).sum := by decide
  have hdescent : baseEnd_8155192 < baseStart_8155192 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8155231 : List Nat := [1, 1, 2, 3, 1, 1, 2, 3, 2, 3, 4]
def baseStart_8155231 : Nat := 118140960795 + 8155231 * 2 ^ 59
def prefixEnd_8155231 : Nat := 4983230072969 + 3 ^ 40 * 8155231 * 2
def baseEnd_8155231 : Nat := 4187553351446887354907281

theorem tailTrace_8155231 : CollatzResearch.WordTrace tailWord_8155231 prefixEnd_8155231 4187553351446887354907281 := by
  unfold tailWord_8155231
  simp only [CollatzResearch.WordTrace]
  refine ⟨297445710717998364413233547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198297140478665576275489031 297445710717998364413233547)
  ·
    refine ⟨446168566076997546619850321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297445710717998364413233547 446168566076997546619850321)
    ·
      refine ⟨334626424557748159964887741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446168566076997546619850321 334626424557748159964887741)
      ·
        refine ⟨125484909209155559986832903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334626424557748159964887741 125484909209155559986832903)
        ·
          refine ⟨188227363813733339980249355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125484909209155559986832903 188227363813733339980249355)
          ·
            refine ⟨282341045720600009970374033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188227363813733339980249355 282341045720600009970374033)
            ·
              refine ⟨211755784290450007477780525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282341045720600009970374033 211755784290450007477780525)
              ·
                refine ⟨79408419108918752804167697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211755784290450007477780525 79408419108918752804167697)
                ·
                  refine ⟨59556314331689064603125773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79408419108918752804167697 59556314331689064603125773)
                  ·
                    refine ⟨22333617874383399226172165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59556314331689064603125773 22333617874383399226172165)
                    ·
                      refine ⟨4187553351446887354907281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22333617874383399226172165 4187553351446887354907281)
                      ·
                        rfl

theorem cell23_8155231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_8155231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155231 prefixEnd_8155231 := by exact prefixLift 8155231
  have htrace : WordTrace (prefixWord ++ tailWord_8155231) baseStart_8155231 baseEnd_8155231 := by
    simpa [prefixWord, tailWord_8155231, baseEnd_8155231] using wordTrace_append hprefix tailTrace_8155231
  have hstable : (prefixWord ++ tailWord_8155231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155231).length < 2 ^ (prefixWord ++ tailWord_8155231).sum := by decide
  have hdescent : baseEnd_8155231 < baseStart_8155231 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8155241 : List Nat := [1, 2, 1, 1, 1, 5, 1, 3, 2, 6]
def baseStart_8155241 : Nat := 118140960795 + 8155241 * 2 ^ 59
def prefixEnd_8155241 : Nat := 4983230072969 + 3 ^ 40 * 8155241 * 2
def baseEnd_8155241 : Nat := 1395852828751144105260745

theorem tailTrace_8155241 : CollatzResearch.WordTrace tailWord_8155241 prefixEnd_8155241 1395852828751144105260745 := by
  unfold tailWord_8155241
  simp only [CollatzResearch.WordTrace]
  refine ⟨297446075447962136121097577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198297383631974757414065051 297446075447962136121097577)
  ·
    refine ⟨223084556585971602090823183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297446075447962136121097577 223084556585971602090823183)
    ·
      refine ⟨334626834878957403136234775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223084556585971602090823183 334626834878957403136234775)
      ·
        refine ⟨501940252318436104704352163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334626834878957403136234775 501940252318436104704352163)
        ·
          refine ⟨752910378477654157056528245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501940252318436104704352163 752910378477654157056528245)
          ·
            refine ⟨70585347982280077224049523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 752910378477654157056528245 70585347982280077224049523)
            ·
              refine ⟨105878021973420115836074285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70585347982280077224049523 105878021973420115836074285)
              ·
                refine ⟨39704258240032543438527857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105878021973420115836074285 39704258240032543438527857)
                ·
                  refine ⟨29778193680024407578895893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39704258240032543438527857 29778193680024407578895893)
                  ·
                    refine ⟨1395852828751144105260745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29778193680024407578895893 1395852828751144105260745)
                    ·
                      rfl

theorem cell23_8155241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 6].length) (baseStart_8155241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155241 prefixEnd_8155241 := by exact prefixLift 8155241
  have htrace : WordTrace (prefixWord ++ tailWord_8155241) baseStart_8155241 baseEnd_8155241 := by
    simpa [prefixWord, tailWord_8155241, baseEnd_8155241] using wordTrace_append hprefix tailTrace_8155241
  have hstable : (prefixWord ++ tailWord_8155241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155241).length < 2 ^ (prefixWord ++ tailWord_8155241).sum := by decide
  have hdescent : baseEnd_8155241 < baseStart_8155241 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8155242 : List Nat := [3, 1, 3, 2, 3, 2, 1, 1, 1, 3, 3]
def baseStart_8155242 : Nat := 118140960795 + 8155242 * 2 ^ 59
def prefixEnd_8155242 : Nat := 4983230072969 + 3 ^ 40 * 8155242 * 2
def baseEnd_8155242 : Nat := 4187558999734086811869731

theorem tailTrace_8155242 : CollatzResearch.WordTrace tailWord_8155242 prefixEnd_8155242 4187558999734086811869731 := by
  unfold tailWord_8155242
  simp only [CollatzResearch.WordTrace]
  refine ⟨74361527980239628322970995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198297407947305675527922653 74361527980239628322970995)
  ·
    refine ⟨111542291970359442484456493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74361527980239628322970995 111542291970359442484456493)
    ·
      refine ⟨41828359488884790931671185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111542291970359442484456493 41828359488884790931671185)
      ·
        refine ⟨31371269616663593198753389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41828359488884790931671185 31371269616663593198753389)
        ·
          refine ⟨11764226106248847449532521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31371269616663593198753389 11764226106248847449532521)
          ·
            refine ⟨8823169579686635587149391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11764226106248847449532521 8823169579686635587149391)
            ·
              refine ⟨13234754369529953380724087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8823169579686635587149391 13234754369529953380724087)
              ·
                refine ⟨19852131554294930071086131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13234754369529953380724087 19852131554294930071086131)
                ·
                  refine ⟨29778197331442395106629197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19852131554294930071086131 29778197331442395106629197)
                  ·
                    refine ⟨11166823999290898164985949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29778197331442395106629197 11166823999290898164985949)
                    ·
                      refine ⟨4187558999734086811869731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11166823999290898164985949 4187558999734086811869731)
                      ·
                        rfl

theorem cell23_8155242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_8155242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155242 prefixEnd_8155242 := by exact prefixLift 8155242
  have htrace : WordTrace (prefixWord ++ tailWord_8155242) baseStart_8155242 baseEnd_8155242 := by
    simpa [prefixWord, tailWord_8155242, baseEnd_8155242] using wordTrace_append hprefix tailTrace_8155242
  have hstable : (prefixWord ++ tailWord_8155242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155242).length < 2 ^ (prefixWord ++ tailWord_8155242).sum := by decide
  have hdescent : baseEnd_8155242 < baseStart_8155242 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8155268 : List Nat := [2, 3, 2, 1, 2, 1, 3, 1, 2, 1, 5]
def baseStart_8155268 : Nat := 118140960795 + 8155268 * 2 ^ 59
def prefixEnd_8155268 : Nat := 4983230072969 + 3 ^ 40 * 8155268 * 2
def baseEnd_8155268 : Nat := 4187572350231103710144611

theorem tailTrace_8155268 : CollatzResearch.WordTrace tailWord_8155268 prefixEnd_8155268 4187572350231103710144611 := by
  unfold tailWord_8155268
  simp only [CollatzResearch.WordTrace]
  refine ⟨148723530109432159866165229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198298040145909546488220305 148723530109432159866165229)
  ·
    refine ⟨55771323791037059949811961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148723530109432159866165229 55771323791037059949811961)
    ·
      refine ⟨41828492843277794962358971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55771323791037059949811961 41828492843277794962358971)
      ·
        refine ⟨62742739264916692443538457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41828492843277794962358971 62742739264916692443538457)
        ·
          refine ⟨47057054448687519332653843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62742739264916692443538457 47057054448687519332653843)
          ·
            refine ⟨70585581673031278998980765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47057054448687519332653843 70585581673031278998980765)
            ·
              refine ⟨26469593127386729624617787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70585581673031278998980765 26469593127386729624617787)
              ·
                refine ⟨39704389691080094436926681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26469593127386729624617787 39704389691080094436926681)
                ·
                  refine ⟨29778292268310070827695011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39704389691080094436926681 29778292268310070827695011)
                  ·
                    refine ⟨44667438402465106241542517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29778292268310070827695011 44667438402465106241542517)
                    ·
                      refine ⟨4187572350231103710144611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44667438402465106241542517 4187572350231103710144611)
                      ·
                        rfl

theorem cell23_8155268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_8155268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155268 prefixEnd_8155268 := by exact prefixLift 8155268
  have htrace : WordTrace (prefixWord ++ tailWord_8155268) baseStart_8155268 baseEnd_8155268 := by
    simpa [prefixWord, tailWord_8155268, baseEnd_8155268] using wordTrace_append hprefix tailTrace_8155268
  have hstable : (prefixWord ++ tailWord_8155268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155268).length < 2 ^ (prefixWord ++ tailWord_8155268).sum := by decide
  have hdescent : baseEnd_8155268 < baseStart_8155268 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8155271 : List Nat := [1, 1, 4, 2, 1, 1, 2, 2, 9]
def baseStart_8155271 : Nat := 118140960795 + 8155271 * 2 ^ 59
def prefixEnd_8155271 : Nat := 4983230072969 + 3 ^ 40 * 8155271 * 2
def baseEnd_8155271 : Nat := 465285987852563022045233

theorem tailTrace_8155271 : CollatzResearch.WordTrace tailWord_8155271 prefixEnd_8155271 465285987852563022045233 := by
  unfold tailWord_8155271
  simp only [CollatzResearch.WordTrace]
  refine ⟨297447169637853451244689667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198298113091902300829793111 297447169637853451244689667)
  ·
    refine ⟨446170754456780176867034501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297447169637853451244689667 446170754456780176867034501)
    ·
      refine ⟨83657016460646283162568969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 446170754456780176867034501 83657016460646283162568969)
      ·
        refine ⟨62742762345484712371926727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83657016460646283162568969 62742762345484712371926727)
        ·
          refine ⟨94114143518227068557890091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62742762345484712371926727 94114143518227068557890091)
          ·
            refine ⟨141171215277340602836835137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94114143518227068557890091 141171215277340602836835137)
            ·
              refine ⟨105878411458005452127626353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141171215277340602836835137 105878411458005452127626353)
              ·
                refine ⟨79408808593504089095719765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105878411458005452127626353 79408808593504089095719765)
                ·
                  refine ⟨465285987852563022045233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 79408808593504089095719765 465285987852563022045233)
                  ·
                    rfl

theorem cell23_8155271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 9].length) (baseStart_8155271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155271 prefixEnd_8155271 := by exact prefixLift 8155271
  have htrace : WordTrace (prefixWord ++ tailWord_8155271) baseStart_8155271 baseEnd_8155271 := by
    simpa [prefixWord, tailWord_8155271, baseEnd_8155271] using wordTrace_append hprefix tailTrace_8155271
  have hstable : (prefixWord ++ tailWord_8155271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155271).length < 2 ^ (prefixWord ++ tailWord_8155271).sum := by decide
  have hdescent : baseEnd_8155271 < baseStart_8155271 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8155282 : List Nat := [3, 2, 3, 1, 1, 1, 1, 3, 4, 2, 2]
def baseStart_8155282 : Nat := 118140960795 + 8155282 * 2 ^ 59
def prefixEnd_8155282 : Nat := 4983230072969 + 3 ^ 40 * 8155282 * 2
def baseEnd_8155282 : Nat := 4187579538960266655369547

theorem tailTrace_8155282 : CollatzResearch.WordTrace tailWord_8155282 prefixEnd_8155282 4187579538960266655369547 := by
  unfold tailWord_8155282
  simp only [CollatzResearch.WordTrace]
  refine ⟨74361892710203400030835025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198298380560542400082226733 74361892710203400030835025)
  ·
    refine ⟨55771419532652550023126269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74361892710203400030835025 55771419532652550023126269)
    ·
      refine ⟨20914282324744706258672351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55771419532652550023126269 20914282324744706258672351)
      ·
        refine ⟨31371423487117059388008527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20914282324744706258672351 31371423487117059388008527)
        ·
          refine ⟨47057135230675589082012791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31371423487117059388008527 47057135230675589082012791)
          ·
            refine ⟨70585702846013383623019187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47057135230675589082012791 70585702846013383623019187)
            ·
              refine ⟨105878554269020075434528781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70585702846013383623019187 105878554269020075434528781)
              ·
                refine ⟨39704457850882528287948293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105878554269020075434528781 39704457850882528287948293)
                ·
                  refine ⟨7444585847040474053990305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39704457850882528287948293 7444585847040474053990305)
                  ·
                    refine ⟨5583439385280355540492729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7444585847040474053990305 5583439385280355540492729)
                    ·
                      refine ⟨4187579538960266655369547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5583439385280355540492729 4187579538960266655369547)
                      ·
                        rfl

theorem cell23_8155282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_8155282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155282 prefixEnd_8155282 := by exact prefixLift 8155282
  have htrace : WordTrace (prefixWord ++ tailWord_8155282) baseStart_8155282 baseEnd_8155282 := by
    simpa [prefixWord, tailWord_8155282, baseEnd_8155282] using wordTrace_append hprefix tailTrace_8155282
  have hstable : (prefixWord ++ tailWord_8155282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155282).length < 2 ^ (prefixWord ++ tailWord_8155282).sum := by decide
  have hdescent : baseEnd_8155282 < baseStart_8155282 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8155311 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 7]
def baseStart_8155311 : Nat := 118140960795 + 8155311 * 2 ^ 59
def prefixEnd_8155311 : Nat := 4983230072969 + 3 ^ 40 * 8155311 * 2
def baseEnd_8155311 : Nat := 4187594429899247041906913

theorem tailTrace_8155311 : CollatzResearch.WordTrace tailWord_8155311 prefixEnd_8155311 4187594429899247041906913 := by
  unfold tailWord_8155311
  simp only [CollatzResearch.WordTrace]
  refine ⟨297448628557708538076145787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198299085705139025384097191 297448628557708538076145787)
  ·
    refine ⟨446172942836562807114218681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297448628557708538076145787 446172942836562807114218681)
    ·
      refine ⟨334629707127422105335664011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446172942836562807114218681 334629707127422105335664011)
      ·
        refine ⟨501944560691133158003496017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334629707127422105335664011 501944560691133158003496017)
        ·
          refine ⟨376458420518349868502622013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 501944560691133158003496017 376458420518349868502622013)
          ·
            refine ⟨141171907694381200688483255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 376458420518349868502622013 141171907694381200688483255)
            ·
              refine ⟨211757861541571801032724883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141171907694381200688483255 211757861541571801032724883)
              ·
                refine ⟨317636792312357701549087325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211757861541571801032724883 317636792312357701549087325)
                ·
                  refine ⟨119113797117134138080907747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 317636792312357701549087325 119113797117134138080907747)
                  ·
                    refine ⟨178670695675701207121361621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 119113797117134138080907747 178670695675701207121361621)
                    ·
                      refine ⟨4187594429899247041906913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 178670695675701207121361621 4187594429899247041906913)
                      ·
                        rfl

theorem cell23_8155311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 7].length) (baseStart_8155311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155311 prefixEnd_8155311 := by exact prefixLift 8155311
  have htrace : WordTrace (prefixWord ++ tailWord_8155311) baseStart_8155311 baseEnd_8155311 := by
    simpa [prefixWord, tailWord_8155311, baseEnd_8155311] using wordTrace_append hprefix tailTrace_8155311
  have hstable : (prefixWord ++ tailWord_8155311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155311).length < 2 ^ (prefixWord ++ tailWord_8155311).sum := by decide
  have hdescent : baseEnd_8155311 < baseStart_8155311 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8155328 : List Nat := [2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 5]
def baseStart_8155328 : Nat := 118140960795 + 8155328 * 2 ^ 59
def prefixEnd_8155328 : Nat := 4983230072969 + 3 ^ 40 * 8155328 * 2
def baseEnd_8155328 : Nat := 4187603159070373475394335

theorem tailTrace_8155328 : CollatzResearch.WordTrace tailWord_8155328 prefixEnd_8155328 4187603159070373475394335 := by
  unfold tailWord_8155328
  simp only [CollatzResearch.WordTrace]
  refine ⟨148724624299323474989757319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198299499065764633319676425 148724624299323474989757319)
  ·
    refine ⟨223086936448985212484635979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148724624299323474989757319 223086936448985212484635979)
    ·
      refine ⟨334630404673477818726953969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223086936448985212484635979 334630404673477818726953969)
      ·
        refine ⟨250972803505108364045215477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334630404673477818726953969 250972803505108364045215477)
        ·
          refine ⟨23528700328603909129238951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 250972803505108364045215477 23528700328603909129238951)
          ·
            refine ⟨35293050492905863693858427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23528700328603909129238951 35293050492905863693858427)
            ·
              refine ⟨52939575739358795540787641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35293050492905863693858427 52939575739358795540787641)
              ·
                refine ⟨39704681804519096655590731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52939575739358795540787641 39704681804519096655590731)
                ·
                  refine ⟨59557022706778644983386097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39704681804519096655590731 59557022706778644983386097)
                  ·
                    refine ⟨44667767030083983737539573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59557022706778644983386097 44667767030083983737539573)
                    ·
                      refine ⟨4187603159070373475394335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44667767030083983737539573 4187603159070373475394335)
                      ·
                        rfl

theorem cell23_8155328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 5].length) (baseStart_8155328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155328 prefixEnd_8155328 := by exact prefixLift 8155328
  have htrace : WordTrace (prefixWord ++ tailWord_8155328) baseStart_8155328 baseEnd_8155328 := by
    simpa [prefixWord, tailWord_8155328, baseEnd_8155328] using wordTrace_append hprefix tailTrace_8155328
  have hstable : (prefixWord ++ tailWord_8155328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155328).length < 2 ^ (prefixWord ++ tailWord_8155328).sum := by decide
  have hdescent : baseEnd_8155328 < baseStart_8155328 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8155331 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 4, 8]
def baseStart_8155331 : Nat := 118140960795 + 8155331 * 2 ^ 59
def prefixEnd_8155331 : Nat := 4983230072969 + 3 ^ 40 * 8155331 * 2
def baseEnd_8155331 : Nat := 1395868233170778987885607

theorem tailTrace_8155331 : CollatzResearch.WordTrace tailWord_8155331 prefixEnd_8155331 1395868233170778987885607 := by
  unfold tailWord_8155331
  simp only [CollatzResearch.WordTrace]
  refine ⟨297449358017636081491873847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198299572011757387661249231 297449358017636081491873847)
  ·
    refine ⟨446174037026454122237810771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297449358017636081491873847 446174037026454122237810771)
    ·
      refine ⟨669261055539681183356716157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446174037026454122237810771 669261055539681183356716157)
      ·
        refine ⟨250972895827380443758768559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 669261055539681183356716157 250972895827380443758768559)
        ·
          refine ⟨376459343741070665638152839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250972895827380443758768559 376459343741070665638152839)
          ·
            refine ⟨564689015611605998457229259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376459343741070665638152839 564689015611605998457229259)
            ·
              refine ⟨847033523417408997685843889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 564689015611605998457229259 847033523417408997685843889)
              ·
                refine ⟨635275142563056748264382917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 847033523417408997685843889 635275142563056748264382917)
                ·
                  refine ⟨119114089230573140299571797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 635275142563056748264382917 119114089230573140299571797)
                  ·
                    refine ⟨1395868233170778987885607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 119114089230573140299571797 1395868233170778987885607)
                    ·
                      rfl

theorem cell23_8155331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 8].length) (baseStart_8155331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155331 prefixEnd_8155331 := by exact prefixLift 8155331
  have htrace : WordTrace (prefixWord ++ tailWord_8155331) baseStart_8155331 baseEnd_8155331 := by
    simpa [prefixWord, tailWord_8155331, baseEnd_8155331] using wordTrace_append hprefix tailTrace_8155331
  have hstable : (prefixWord ++ tailWord_8155331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155331).length < 2 ^ (prefixWord ++ tailWord_8155331).sum := by decide
  have hdescent : baseEnd_8155331 < baseStart_8155331 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8155365 : List Nat := [1, 3, 1, 4, 2, 1, 1, 1, 5, 4]
def baseStart_8155365 : Nat := 118140960795 + 8155365 * 2 ^ 59
def prefixEnd_8155365 : Nat := 4983230072969 + 3 ^ 40 * 8155365 * 2
def baseEnd_8155365 : Nat := 1395874052618196610210555

theorem tailTrace_8155365 : CollatzResearch.WordTrace tailWord_8155365 prefixEnd_8155365 1395874052618196610210555 := by
  unfold tailWord_8155365
  simp only [CollatzResearch.WordTrace]
  refine ⟨297450598099512905298611549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198300398733008603532407699 297450598099512905298611549)
  ·
    refine ⟨111543974287317339486979331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297450598099512905298611549 111543974287317339486979331)
    ·
      refine ⟨167315961430976009230468997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111543974287317339486979331 167315961430976009230468997)
      ·
        refine ⟨31371742768308001730712937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167315961430976009230468997 31371742768308001730712937)
        ·
          refine ⟨23528807076231001298034703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31371742768308001730712937 23528807076231001298034703)
          ·
            refine ⟨35293210614346501947052055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23528807076231001298034703 35293210614346501947052055)
            ·
              refine ⟨52939815921519752920578083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35293210614346501947052055 52939815921519752920578083)
              ·
                refine ⟨79409723882279629380867125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52939815921519752920578083 79409723882279629380867125)
                ·
                  refine ⟨7444661613963715254456293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79409723882279629380867125 7444661613963715254456293)
                  ·
                    refine ⟨1395874052618196610210555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7444661613963715254456293 1395874052618196610210555)
                    ·
                      rfl

theorem cell23_8155365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 5, 4].length) (baseStart_8155365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155365 prefixEnd_8155365 := by exact prefixLift 8155365
  have htrace : WordTrace (prefixWord ++ tailWord_8155365) baseStart_8155365 baseEnd_8155365 := by
    simpa [prefixWord, tailWord_8155365, baseEnd_8155365] using wordTrace_append hprefix tailTrace_8155365
  have hstable : (prefixWord ++ tailWord_8155365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155365).length < 2 ^ (prefixWord ++ tailWord_8155365).sum := by decide
  have hdescent : baseEnd_8155365 < baseStart_8155365 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8155375 : List Nat := [1, 1, 2, 1, 6, 2, 1, 1, 1, 4, 3]
def baseStart_8155375 : Nat := 118140960795 + 8155375 * 2 ^ 59
def prefixEnd_8155375 : Nat := 4983230072969 + 3 ^ 40 * 8155375 * 2
def baseEnd_8155375 : Nat := 4187627292661134791506619

theorem tailTrace_8155375 : CollatzResearch.WordTrace tailWord_8155375 prefixEnd_8155375 4187627292661134791506619 := by
  unfold tailWord_8155375
  simp only [CollatzResearch.WordTrace]
  refine ⟨297450962829476677006475579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198300641886317784670983719 297450962829476677006475579)
  ·
    refine ⟨446176444244215015509713369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297450962829476677006475579 446176444244215015509713369)
    ·
      refine ⟨334632333183161261632285027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446176444244215015509713369 334632333183161261632285027)
      ·
        refine ⟨501948499774741892448427541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334632333183161261632285027 501948499774741892448427541)
        ·
          refine ⟨23528835926941026208520041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 501948499774741892448427541 23528835926941026208520041)
          ·
            refine ⟨17646626945205769656390031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23528835926941026208520041 17646626945205769656390031)
            ·
              refine ⟨26469940417808654484585047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17646626945205769656390031 26469940417808654484585047)
              ·
                refine ⟨39704910626712981726877571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26469940417808654484585047 39704910626712981726877571)
                ·
                  refine ⟨59557365940069472590316357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39704910626712981726877571 59557365940069472590316357)
                  ·
                    refine ⟨11167006113763026110684317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59557365940069472590316357 11167006113763026110684317)
                    ·
                      refine ⟨4187627292661134791506619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11167006113763026110684317 4187627292661134791506619)
                      ·
                        rfl

theorem cell23_8155375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 4, 3].length) (baseStart_8155375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155375 prefixEnd_8155375 := by exact prefixLift 8155375
  have htrace : WordTrace (prefixWord ++ tailWord_8155375) baseStart_8155375 baseEnd_8155375 := by
    simpa [prefixWord, tailWord_8155375, baseEnd_8155375] using wordTrace_append hprefix tailTrace_8155375
  have hstable : (prefixWord ++ tailWord_8155375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155375).length < 2 ^ (prefixWord ++ tailWord_8155375).sum := by decide
  have hdescent : baseEnd_8155375 < baseStart_8155375 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8155399 : List Nat := [1, 1, 4, 5, 1, 1, 2, 1, 3, 4]
def baseStart_8155399 : Nat := 118140960795 + 8155399 * 2 ^ 59
def prefixEnd_8155399 : Nat := 4983230072969 + 3 ^ 40 * 8155399 * 2
def baseEnd_8155399 : Nat := 1395879872065614232535503

theorem tailTrace_8155399 : CollatzResearch.WordTrace tailWord_8155399 prefixEnd_8155399 1395879872065614232535503 := by
  unfold tailWord_8155399
  simp only [CollatzResearch.WordTrace]
  refine ⟨297451838181389729105349251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198301225454259819403566167 297451838181389729105349251)
  ·
    refine ⟨446177757272084593658023877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297451838181389729105349251 446177757272084593658023877)
    ·
      refine ⟨83658329488515861310879477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 446177757272084593658023877 83658329488515861310879477)
      ·
        refine ⟨7842968389548361997894951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83658329488515861310879477 7842968389548361997894951)
        ·
          refine ⟨11764452584322542996842427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7842968389548361997894951 11764452584322542996842427)
          ·
            refine ⟨17646678876483814495263641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11764452584322542996842427 17646678876483814495263641)
            ·
              refine ⟨13235009157362860871447731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17646678876483814495263641 13235009157362860871447731)
              ·
                refine ⟨19852513736044291307171597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13235009157362860871447731 19852513736044291307171597)
                ·
                  refine ⟨7444692651016609240189349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19852513736044291307171597 7444692651016609240189349)
                  ·
                    refine ⟨1395879872065614232535503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7444692651016609240189349 1395879872065614232535503)
                    ·
                      rfl

theorem cell23_8155399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 3, 4].length) (baseStart_8155399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155399 prefixEnd_8155399 := by exact prefixLift 8155399
  have htrace : WordTrace (prefixWord ++ tailWord_8155399) baseStart_8155399 baseEnd_8155399 := by
    simpa [prefixWord, tailWord_8155399, baseEnd_8155399] using wordTrace_append hprefix tailTrace_8155399
  have hstable : (prefixWord ++ tailWord_8155399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155399).length < 2 ^ (prefixWord ++ tailWord_8155399).sum := by decide
  have hdescent : baseEnd_8155399 < baseStart_8155399 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8155425 : List Nat := [1, 2, 3, 2, 1, 1, 3, 4, 1, 5]
def baseStart_8155425 : Nat := 118140960795 + 8155425 * 2 ^ 59
def prefixEnd_8155425 : Nat := 4983230072969 + 3 ^ 40 * 8155425 * 2
def baseEnd_8155425 : Nat := 1395884322231286531960463

theorem tailTrace_8155425 : CollatzResearch.WordTrace tailWord_8155425 prefixEnd_8155425 1395884322231286531960463 := by
  unfold tailWord_8155425
  simp only [CollatzResearch.WordTrace]
  refine ⟨297452786479295535545795729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198301857652863690363863819 297452786479295535545795729)
  ·
    refine ⟨223089589859471651659346797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297452786479295535545795729 223089589859471651659346797)
    ·
      refine ⟨83658596197301869372255049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223089589859471651659346797 83658596197301869372255049)
      ·
        refine ⟨62743947147976402029191287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83658596197301869372255049 62743947147976402029191287)
        ·
          refine ⟨94115920721964603043786931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62743947147976402029191287 94115920721964603043786931)
          ·
            refine ⟨141173881082946904565680397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94115920721964603043786931 141173881082946904565680397)
            ·
              refine ⟨52940205406105089212130149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141173881082946904565680397 52940205406105089212130149)
              ·
                refine ⟨9926288513644704227274403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52940205406105089212130149 9926288513644704227274403)
                ·
                  refine ⟨14889432770467056340911605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9926288513644704227274403 14889432770467056340911605)
                  ·
                    refine ⟨1395884322231286531960463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14889432770467056340911605 1395884322231286531960463)
                    ·
                      rfl

theorem cell23_8155425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 4, 1, 5].length) (baseStart_8155425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155425 prefixEnd_8155425 := by exact prefixLift 8155425
  have htrace : WordTrace (prefixWord ++ tailWord_8155425) baseStart_8155425 baseEnd_8155425 := by
    simpa [prefixWord, tailWord_8155425, baseEnd_8155425] using wordTrace_append hprefix tailTrace_8155425
  have hstable : (prefixWord ++ tailWord_8155425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155425).length < 2 ^ (prefixWord ++ tailWord_8155425).sum := by decide
  have hdescent : baseEnd_8155425 < baseStart_8155425 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8155439 : List Nat := [1, 1, 2, 1, 2, 1, 7, 3, 1, 1, 3]
def baseStart_8155439 : Nat := 118140960795 + 8155439 * 2 ^ 59
def prefixEnd_8155439 : Nat := 4983230072969 + 3 ^ 40 * 8155439 * 2
def baseEnd_8155439 : Nat := 4187660155423022541106325

theorem tailTrace_8155439 : CollatzResearch.WordTrace tailWord_8155439 prefixEnd_8155439 4187660155423022541106325 := by
  unfold tailWord_8155439
  simp only [CollatzResearch.WordTrace]
  refine ⟨297453297101244815936805371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198302198067496543957870247 297453297101244815936805371)
  ·
    refine ⟨446179945651867223905208057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297453297101244815936805371 446179945651867223905208057)
    ·
      refine ⟨334634959238900417928906043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446179945651867223905208057 334634959238900417928906043)
      ·
        refine ⟨501952438858350626893359065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334634959238900417928906043 501952438858350626893359065)
        ·
          refine ⟨376464329143762970170019299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 501952438858350626893359065 376464329143762970170019299)
          ·
            refine ⟨564696493715644455255028949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376464329143762970170019299 564696493715644455255028949)
            ·
              refine ⟨13235074071460416920039741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 564696493715644455255028949 13235074071460416920039741)
              ·
                refine ⟨4963152776797656345014903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13235074071460416920039741 4963152776797656345014903)
                ·
                  refine ⟨7444729165196484517522355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4963152776797656345014903 7444729165196484517522355)
                  ·
                    refine ⟨11167093747794726776283533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7444729165196484517522355 11167093747794726776283533)
                    ·
                      refine ⟨4187660155423022541106325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11167093747794726776283533 4187660155423022541106325)
                      ·
                        rfl

theorem cell23_8155439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 3, 1, 1, 3].length) (baseStart_8155439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155439 prefixEnd_8155439 := by exact prefixLift 8155439
  have htrace : WordTrace (prefixWord ++ tailWord_8155439) baseStart_8155439 baseEnd_8155439 := by
    simpa [prefixWord, tailWord_8155439, baseEnd_8155439] using wordTrace_append hprefix tailTrace_8155439
  have hstable : (prefixWord ++ tailWord_8155439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155439).length < 2 ^ (prefixWord ++ tailWord_8155439).sum := by decide
  have hdescent : baseEnd_8155439 < baseStart_8155439 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8155449 : List Nat := [1, 2, 1, 6, 1, 2, 1, 2, 2, 3, 2]
def baseStart_8155449 : Nat := 118140960795 + 8155449 * 2 ^ 59
def prefixEnd_8155449 : Nat := 4983230072969 + 3 ^ 40 * 8155449 * 2
def baseEnd_8155449 : Nat := 4187665290229567501981279

theorem tailTrace_8155449 : CollatzResearch.WordTrace tailWord_8155449 prefixEnd_8155449 4187665290229567501981279 := by
  unfold tailWord_8155449
  simp only [CollatzResearch.WordTrace]
  refine ⟨297453661831208587644669401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198302441220805725096446267 297453661831208587644669401)
  ·
    refine ⟨223090246373406440733502051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297453661831208587644669401 223090246373406440733502051)
    ·
      refine ⟨334635369560109661100253077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223090246373406440733502051 334635369560109661100253077)
      ·
        refine ⟨15686032948130140364074363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 334635369560109661100253077 15686032948130140364074363)
        ·
          refine ⟨23529049422195210546111545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15686032948130140364074363 23529049422195210546111545)
          ·
            refine ⟨17646787066646407909583659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23529049422195210546111545 17646787066646407909583659)
            ·
              refine ⟨26470180599969611864375489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17646787066646407909583659 26470180599969611864375489)
              ·
                refine ⟨19852635449977208898281617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26470180599969611864375489 19852635449977208898281617)
                ·
                  refine ⟨14889476587482906673711213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19852635449977208898281617 14889476587482906673711213)
                  ·
                    refine ⟨5583553720306090002641705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14889476587482906673711213 5583553720306090002641705)
                    ·
                      refine ⟨4187665290229567501981279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5583553720306090002641705 4187665290229567501981279)
                      ·
                        rfl

theorem cell23_8155449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_8155449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155449 prefixEnd_8155449 := by exact prefixLift 8155449
  have htrace : WordTrace (prefixWord ++ tailWord_8155449) baseStart_8155449 baseEnd_8155449 := by
    simpa [prefixWord, tailWord_8155449, baseEnd_8155449] using wordTrace_append hprefix tailTrace_8155449
  have hstable : (prefixWord ++ tailWord_8155449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155449).length < 2 ^ (prefixWord ++ tailWord_8155449).sum := by decide
  have hdescent : baseEnd_8155449 < baseStart_8155449 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8155455 : List Nat := [1, 1, 2, 2, 4, 1, 1, 3, 4, 4]
def baseStart_8155455 : Nat := 118140960795 + 8155455 * 2 ^ 59
def prefixEnd_8155455 : Nat := 4983230072969 + 3 ^ 40 * 8155455 * 2
def baseEnd_8155455 : Nat := 1395889457037831492835417

theorem tailTrace_8155455 : CollatzResearch.WordTrace tailWord_8155455 prefixEnd_8155455 1395889457037831492835417 := by
  unfold tailWord_8155455
  simp only [CollatzResearch.WordTrace]
  refine ⟨297453880669186850669387819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198302587112791233779591879 297453880669186850669387819)
  ·
    refine ⟨446180821003780276004081729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297453880669186850669387819 446180821003780276004081729)
    ·
      refine ⟨334635615752835207003061297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446180821003780276004081729 334635615752835207003061297)
      ·
        refine ⟨250976711814626405252295973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334635615752835207003061297 250976711814626405252295973)
        ·
          refine ⟨47058133465242450984805495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 250976711814626405252295973 47058133465242450984805495)
          ·
            refine ⟨70587200197863676477208243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47058133465242450984805495 70587200197863676477208243)
            ·
              refine ⟨105880800296795514715812365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70587200197863676477208243 105880800296795514715812365)
              ·
                refine ⟨39705300111298318018429637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105880800296795514715812365 39705300111298318018429637)
                ·
                  refine ⟨7444743770868434628455557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39705300111298318018429637 7444743770868434628455557)
                  ·
                    refine ⟨1395889457037831492835417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7444743770868434628455557 1395889457037831492835417)
                    ·
                      rfl

theorem cell23_8155455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 4, 4].length) (baseStart_8155455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155455 prefixEnd_8155455 := by exact prefixLift 8155455
  have htrace : WordTrace (prefixWord ++ tailWord_8155455) baseStart_8155455 baseEnd_8155455 := by
    simpa [prefixWord, tailWord_8155455, baseEnd_8155455] using wordTrace_append hprefix tailTrace_8155455
  have hstable : (prefixWord ++ tailWord_8155455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155455).length < 2 ^ (prefixWord ++ tailWord_8155455).sum := by decide
  have hdescent : baseEnd_8155455 < baseStart_8155455 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8155465 : List Nat := [1, 2, 1, 1, 2, 3, 1, 4, 3, 2, 3]
def baseStart_8155465 : Nat := 118140960795 + 8155465 * 2 ^ 59
def prefixEnd_8155465 : Nat := 4983230072969 + 3 ^ 40 * 8155465 * 2
def baseEnd_8155465 : Nat := 4187673505920039439381205

theorem tailTrace_8155465 : CollatzResearch.WordTrace tailWord_8155465 prefixEnd_8155465 4187673505920039439381205 := by
  unfold tailWord_8155465
  simp only [CollatzResearch.WordTrace]
  refine ⟨297454245399150622377251849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198302830266100414918167899 297454245399150622377251849)
  ·
    refine ⟨223090684049362966782938887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297454245399150622377251849 223090684049362966782938887)
    ·
      refine ⟨334636026074044450174408331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223090684049362966782938887 334636026074044450174408331)
      ·
        refine ⟨501954039111066675261612497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334636026074044450174408331 501954039111066675261612497)
        ·
          refine ⟨376465529333300006446209373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 501954039111066675261612497 376465529333300006446209373)
          ·
            refine ⟨141174573499987502417328515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 376465529333300006446209373 141174573499987502417328515)
            ·
              refine ⟨211761860249981253625992773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141174573499987502417328515 211761860249981253625992773)
              ·
                refine ⟨39705348796871485054873645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 211761860249981253625992773 39705348796871485054873645)
                ·
                  refine ⟨14889505798826806895577617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39705348796871485054873645 14889505798826806895577617)
                  ·
                    refine ⟨11167129349120105171683213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14889505798826806895577617 11167129349120105171683213)
                    ·
                      refine ⟨4187673505920039439381205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11167129349120105171683213 4187673505920039439381205)
                      ·
                        rfl

theorem cell23_8155465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 3, 2, 3].length) (baseStart_8155465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155465 prefixEnd_8155465 := by exact prefixLift 8155465
  have htrace : WordTrace (prefixWord ++ tailWord_8155465) baseStart_8155465 baseEnd_8155465 := by
    simpa [prefixWord, tailWord_8155465, baseEnd_8155465] using wordTrace_append hprefix tailTrace_8155465
  have hstable : (prefixWord ++ tailWord_8155465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155465).length < 2 ^ (prefixWord ++ tailWord_8155465).sum := by decide
  have hdescent : baseEnd_8155465 < baseStart_8155465 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8155472 : List Nat := [2, 1, 1, 1, 1, 7, 1, 3, 2, 4]
def baseStart_8155472 : Nat := 118140960795 + 8155472 * 2 ^ 59
def prefixEnd_8155472 : Nat := 4983230072969 + 3 ^ 40 * 8155472 * 2
def baseEnd_8155472 : Nat := 1395892366761540303997891

theorem tailTrace_8155472 : CollatzResearch.WordTrace tailWord_8155472 prefixEnd_8155472 1395892366761540303997891 := by
  unfold tailWord_8155472
  simp only [CollatzResearch.WordTrace]
  refine ⟨148727250355062631286378335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198303000473416841715171113 148727250355062631286378335)
  ·
    refine ⟨223090875532593946929567503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148727250355062631286378335 223090875532593946929567503)
    ·
      refine ⟨334636313298890920394351255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223090875532593946929567503 334636313298890920394351255)
      ·
        refine ⟨501954469948336380591526883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334636313298890920394351255 501954469948336380591526883)
        ·
          refine ⟨752931704922504570887290325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501954469948336380591526883 752931704922504570887290325)
          ·
            refine ⟨17646836834121200880170867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 752931704922504570887290325 17646836834121200880170867)
            ·
              refine ⟨26470255251181801320256301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17646836834121200880170867 26470255251181801320256301)
              ·
                refine ⟨9926345719193175495096113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26470255251181801320256301 9926345719193175495096113)
                ·
                  refine ⟨7444759289394881621322085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9926345719193175495096113 7444759289394881621322085)
                  ·
                    refine ⟨1395892366761540303997891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7444759289394881621322085 1395892366761540303997891)
                    ·
                      rfl

theorem cell23_8155472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 3, 2, 4].length) (baseStart_8155472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155472 prefixEnd_8155472 := by exact prefixLift 8155472
  have htrace : WordTrace (prefixWord ++ tailWord_8155472) baseStart_8155472 baseEnd_8155472 := by
    simpa [prefixWord, tailWord_8155472, baseEnd_8155472] using wordTrace_append hprefix tailTrace_8155472
  have hstable : (prefixWord ++ tailWord_8155472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155472).length < 2 ^ (prefixWord ++ tailWord_8155472).sum := by decide
  have hdescent : baseEnd_8155472 < baseStart_8155472 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8155529 : List Nat := [1, 2, 1, 1, 6, 1, 2, 3, 2, 1, 3]
def baseStart_8155529 : Nat := 118140960795 + 8155529 * 2 ^ 59
def prefixEnd_8155529 : Nat := 4983230072969 + 3 ^ 40 * 8155529 * 2
def baseEnd_8155529 : Nat := 4187706368681927188980911

theorem tailTrace_8155529 : CollatzResearch.WordTrace tailWord_8155529 prefixEnd_8155529 4187706368681927188980911 := by
  unfold tailWord_8155529
  simp only [CollatzResearch.WordTrace]
  refine ⟨297456579670918761307581641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198304386447279174205054427 297456579670918761307581641)
  ·
    refine ⟨223092434753189070980686231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297456579670918761307581641 223092434753189070980686231)
    ·
      refine ⟨334638652129783606471029347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223092434753189070980686231 334638652129783606471029347)
      ·
        refine ⟨501957978194675409706544021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334638652129783606471029347 501957978194675409706544021)
        ·
          refine ⟨23529280227875409829994251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 501957978194675409706544021 23529280227875409829994251)
          ·
            refine ⟨35293920341813114744991377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23529280227875409829994251 35293920341813114744991377)
            ·
              refine ⟨26470440256359836058743533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35293920341813114744991377 26470440256359836058743533)
              ·
                refine ⟨9926415096134938522028825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26470440256359836058743533 9926415096134938522028825)
                ·
                  refine ⟨7444811322101203891521619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9926415096134938522028825 7444811322101203891521619)
                  ·
                    refine ⟨11167216983151805837282429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7444811322101203891521619 11167216983151805837282429)
                    ·
                      refine ⟨4187706368681927188980911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11167216983151805837282429 4187706368681927188980911)
                      ·
                        rfl

theorem cell23_8155529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 3, 2, 1, 3].length) (baseStart_8155529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155529 prefixEnd_8155529 := by exact prefixLift 8155529
  have htrace : WordTrace (prefixWord ++ tailWord_8155529) baseStart_8155529 baseEnd_8155529 := by
    simpa [prefixWord, tailWord_8155529, baseEnd_8155529] using wordTrace_append hprefix tailTrace_8155529
  have hstable : (prefixWord ++ tailWord_8155529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155529).length < 2 ^ (prefixWord ++ tailWord_8155529).sum := by decide
  have hdescent : baseEnd_8155529 < baseStart_8155529 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8155556 : List Nat := [2, 3, 1, 2, 1, 1, 6, 1, 1, 3, 2]
def baseStart_8155556 : Nat := 118140960795 + 8155556 * 2 ^ 59
def prefixEnd_8155556 : Nat := 4983230072969 + 3 ^ 40 * 8155556 * 2
def baseEnd_8155556 : Nat := 4187720232659598583343287

theorem tailTrace_8155556 : CollatzResearch.WordTrace tailWord_8155556 prefixEnd_8155556 4187720232659598583343287 := by
  unfold tailWord_8155556
  simp only [CollatzResearch.WordTrace]
  refine ⟨148728782220910472459407261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198305042961213963279209681 148728782220910472459407261)
  ·
    refine ⟨55773293332841427172277723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148728782220910472459407261 55773293332841427172277723)
    ·
      refine ⟨83659939999262140758416585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55773293332841427172277723 83659939999262140758416585)
      ·
        refine ⟨62744954999446605568812439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83659939999262140758416585 62744954999446605568812439)
        ·
          refine ⟨94117432499169908353218659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62744954999446605568812439 94117432499169908353218659)
          ·
            refine ⟨141176148748754862529827989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94117432499169908353218659 141176148748754862529827989)
            ·
              refine ⟨6617631972597884181085687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 141176148748754862529827989 6617631972597884181085687)
              ·
                refine ⟨9926447958896826271628531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6617631972597884181085687 9926447958896826271628531)
                ·
                  refine ⟨14889671938345239407442797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9926447958896826271628531 14889671938345239407442797)
                  ·
                    refine ⟨5583626976879464777791049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14889671938345239407442797 5583626976879464777791049)
                    ·
                      refine ⟨4187720232659598583343287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5583626976879464777791049 4187720232659598583343287)
                      ·
                        rfl

theorem cell23_8155556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 1, 1, 3, 2].length) (baseStart_8155556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155556 prefixEnd_8155556 := by exact prefixLift 8155556
  have htrace : WordTrace (prefixWord ++ tailWord_8155556) baseStart_8155556 baseEnd_8155556 := by
    simpa [prefixWord, tailWord_8155556, baseEnd_8155556] using wordTrace_append hprefix tailTrace_8155556
  have hstable : (prefixWord ++ tailWord_8155556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155556).length < 2 ^ (prefixWord ++ tailWord_8155556).sum := by decide
  have hdescent : baseEnd_8155556 < baseStart_8155556 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8155575 : List Nat := [1, 1, 3, 1, 3, 3, 1, 3, 7]
def baseStart_8155575 : Nat := 118140960795 + 8155575 * 2 ^ 59
def prefixEnd_8155575 : Nat := 4983230072969 + 3 ^ 40 * 8155575 * 2
def baseEnd_8155575 : Nat := 465303332088003778778411

theorem tailTrace_8155575 : CollatzResearch.WordTrace tailWord_8155575 prefixEnd_8155575 465303332088003778778411 := by
  unfold tailWord_8155575
  simp only [CollatzResearch.WordTrace]
  refine ⟨297458257428752111163756179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198305504952501407442504119 297458257428752111163756179)
  ·
    refine ⟨446187386143128166745634269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297458257428752111163756179 446187386143128166745634269)
    ·
      refine ⟨167320269803673062529612851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 446187386143128166745634269 167320269803673062529612851)
      ·
        refine ⟨250980404705509593794419277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167320269803673062529612851 250980404705509593794419277)
        ·
          refine ⟨94117651764566097672907229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250980404705509593794419277 94117651764566097672907229)
          ·
            refine ⟨35294119411712286627340211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94117651764566097672907229 35294119411712286627340211)
            ·
              refine ⟨52941179117568429941010317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35294119411712286627340211 52941179117568429941010317)
              ·
                refine ⟨19852942169088161227878869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52941179117568429941010317 19852942169088161227878869)
                ·
                  refine ⟨465303332088003778778411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19852942169088161227878869 465303332088003778778411)
                  ·
                    rfl

theorem cell23_8155575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 7].length) (baseStart_8155575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155575 prefixEnd_8155575 := by exact prefixLift 8155575
  have htrace : WordTrace (prefixWord ++ tailWord_8155575) baseStart_8155575 baseEnd_8155575 := by
    simpa [prefixWord, tailWord_8155575, baseEnd_8155575] using wordTrace_append hprefix tailTrace_8155575
  have hstable : (prefixWord ++ tailWord_8155575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155575).length < 2 ^ (prefixWord ++ tailWord_8155575).sum := by decide
  have hdescent : baseEnd_8155575 < baseStart_8155575 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8155582 : List Nat := [4, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4]
def baseStart_8155582 : Nat := 118140960795 + 8155582 * 2 ^ 59
def prefixEnd_8155582 : Nat := 4983230072969 + 3 ^ 40 * 8155582 * 2
def baseEnd_8155582 : Nat := 4187733583156615481618167

theorem tailTrace_8155582 : CollatzResearch.WordTrace tailWord_8155582 prefixEnd_8155582 4187733583156615481618167 := by
  unfold tailWord_8155582
  simp only [CollatzResearch.WordTrace]
  refine ⟨37182314092465843919907625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198305675159817834239507333 37182314092465843919907625)
  ·
    refine ⟨27886735569349382939930719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37182314092465843919907625 27886735569349382939930719)
    ·
      refine ⟨41830103354024074409896079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27886735569349382939930719 41830103354024074409896079)
      ·
        refine ⟨62745155031036111614844119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41830103354024074409896079 62745155031036111614844119)
        ·
          refine ⟨94117732546554167422266179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62745155031036111614844119 94117732546554167422266179)
          ·
            refine ⟨141176598819831251133399269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94117732546554167422266179 141176598819831251133399269)
            ·
              refine ⟨26470612278718359587512363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141176598819831251133399269 26470612278718359587512363)
              ·
                refine ⟨39705918418077539381268545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26470612278718359587512363 39705918418077539381268545)
                ·
                  refine ⟨29779438813558154535951409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39705918418077539381268545 29779438813558154535951409)
                  ·
                    refine ⟨22334579110168615901963557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29779438813558154535951409 22334579110168615901963557)
                    ·
                      refine ⟨4187733583156615481618167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22334579110168615901963557 4187733583156615481618167)
                      ·
                        rfl

theorem cell23_8155582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_8155582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155582 prefixEnd_8155582 := by exact prefixLift 8155582
  have htrace : WordTrace (prefixWord ++ tailWord_8155582) baseStart_8155582 baseEnd_8155582 := by
    simpa [prefixWord, tailWord_8155582, baseEnd_8155582] using wordTrace_append hprefix tailTrace_8155582
  have hstable : (prefixWord ++ tailWord_8155582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155582).length < 2 ^ (prefixWord ++ tailWord_8155582).sum := by decide
  have hdescent : baseEnd_8155582 < baseStart_8155582 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8155625 : List Nat := [1, 2, 1, 1, 1, 2, 1, 4, 3, 3, 4]
def baseStart_8155625 : Nat := 118140960795 + 8155625 * 2 ^ 59
def prefixEnd_8155625 : Nat := 4983230072969 + 3 ^ 40 * 8155625 * 2
def baseEnd_8155625 : Nat := 4187755662824758813380469

theorem tailTrace_8155625 : CollatzResearch.WordTrace tailWord_8155625 prefixEnd_8155625 4187755662824758813380469 := by
  unfold tailWord_8155625
  simp only [CollatzResearch.WordTrace]
  refine ⟨297460081078570969703076329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198306720719047313135384219 297460081078570969703076329)
  ·
    refine ⟨223095060808928227277307247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297460081078570969703076329 223095060808928227277307247)
    ·
      refine ⟨334642591213392340915960871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223095060808928227277307247 334642591213392340915960871)
      ·
        refine ⟨501963886820088511373941307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334642591213392340915960871 501963886820088511373941307)
        ·
          refine ⟨752945830230132767060911961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501963886820088511373941307 752945830230132767060911961)
          ·
            refine ⟨564709372672599575295683971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 752945830230132767060911961 564709372672599575295683971)
            ·
              refine ⟨847064059008899362943525957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 564709372672599575295683971 847064059008899362943525957)
              ·
                refine ⟨158824511064168630551911117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 847064059008899362943525957 158824511064168630551911117)
                ·
                  refine ⟨59559191649063236456966669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158824511064168630551911117 59559191649063236456966669)
                  ·
                    refine ⟨22334696868398713671362501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59559191649063236456966669 22334696868398713671362501)
                    ·
                      refine ⟨4187755662824758813380469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22334696868398713671362501 4187755662824758813380469)
                      ·
                        rfl

theorem cell23_8155625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 3, 4].length) (baseStart_8155625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155625 prefixEnd_8155625 := by exact prefixLift 8155625
  have htrace : WordTrace (prefixWord ++ tailWord_8155625) baseStart_8155625 baseEnd_8155625 := by
    simpa [prefixWord, tailWord_8155625, baseEnd_8155625] using wordTrace_append hprefix tailTrace_8155625
  have hstable : (prefixWord ++ tailWord_8155625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155625).length < 2 ^ (prefixWord ++ tailWord_8155625).sum := by decide
  have hdescent : baseEnd_8155625 < baseStart_8155625 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8155626 : List Nat := [3, 1, 3, 1, 3, 2, 3, 2, 5]
def baseStart_8155626 : Nat := 118140960795 + 8155626 * 2 ^ 59
def prefixEnd_8155626 : Nat := 4983230072969 + 3 ^ 40 * 8155626 * 2
def baseEnd_8155626 : Nat := 465306241811712589940885

theorem tailTrace_8155626 : CollatzResearch.WordTrace tailWord_8155626 prefixEnd_8155626 465306241811712589940885 := by
  unfold tailWord_8155626
  simp only [CollatzResearch.WordTrace]
  refine ⟨74365029387891836718465683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198306745034378231249241821 74365029387891836718465683)
  ·
    refine ⟨111547544081837755077698525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74365029387891836718465683 111547544081837755077698525)
    ·
      refine ⟨41830329030689158154136947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111547544081837755077698525 41830329030689158154136947)
      ·
        refine ⟨62745493546033737231205421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41830329030689158154136947 62745493546033737231205421)
        ·
          refine ⟨23529560079762651461702033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62745493546033737231205421 23529560079762651461702033)
          ·
            refine ⟨17647170059821988596276525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23529560079762651461702033 17647170059821988596276525)
            ·
              refine ⟨6617688772433245723603697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17647170059821988596276525 6617688772433245723603697)
              ·
                refine ⟨4963266579324934292702773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6617688772433245723603697 4963266579324934292702773)
                ·
                  refine ⟨465306241811712589940885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4963266579324934292702773 465306241811712589940885)
                  ·
                    rfl

theorem cell23_8155626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 2, 5].length) (baseStart_8155626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155626 prefixEnd_8155626 := by exact prefixLift 8155626
  have htrace : WordTrace (prefixWord ++ tailWord_8155626) baseStart_8155626 baseEnd_8155626 := by
    simpa [prefixWord, tailWord_8155626, baseEnd_8155626] using wordTrace_append hprefix tailTrace_8155626
  have hstable : (prefixWord ++ tailWord_8155626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155626).length < 2 ^ (prefixWord ++ tailWord_8155626).sum := by decide
  have hdescent : baseEnd_8155626 < baseStart_8155626 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8155637 : List Nat := [1, 3, 5, 1, 2, 2, 2, 1, 2, 2, 2]
def baseStart_8155637 : Nat := 118140960795 + 8155637 * 2 ^ 59
def prefixEnd_8155637 : Nat := 4983230072969 + 3 ^ 40 * 8155637 * 2
def baseEnd_8155637 : Nat := 4187761824592612766430415

theorem tailTrace_8155637 : CollatzResearch.WordTrace tailWord_8155637 prefixEnd_8155637 4187761824592612766430415 := by
  unfold tailWord_8155637
  simp only [CollatzResearch.WordTrace]
  refine ⟨297460518754527495752513165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198307012503018330501675443 297460518754527495752513165)
  ·
    refine ⟨111547694532947810907192437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 297460518754527495752513165 111547694532947810907192437)
    ·
      refine ⟨10457596362463857272549291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111547694532947810907192437 10457596362463857272549291)
      ·
        refine ⟨15686394543695785908823937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10457596362463857272549291 15686394543695785908823937)
        ·
          refine ⟨11764795907771839431617953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15686394543695785908823937 11764795907771839431617953)
          ·
            refine ⟨8823596930828879573713465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11764795907771839431617953 8823596930828879573713465)
            ·
              refine ⟨6617697698121659680285099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8823596930828879573713465 6617697698121659680285099)
              ·
                refine ⟨9926546547182489520427649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6617697698121659680285099 9926546547182489520427649)
                ·
                  refine ⟨7444909910386867140320737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9926546547182489520427649 7444909910386867140320737)
                  ·
                    refine ⟨5583682432790150355240553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7444909910386867140320737 5583682432790150355240553)
                    ·
                      refine ⟨4187761824592612766430415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5583682432790150355240553 4187761824592612766430415)
                      ·
                        rfl

theorem cell23_8155637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_8155637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155637 prefixEnd_8155637 := by exact prefixLift 8155637
  have htrace : WordTrace (prefixWord ++ tailWord_8155637) baseStart_8155637 baseEnd_8155637 := by
    simpa [prefixWord, tailWord_8155637, baseEnd_8155637] using wordTrace_append hprefix tailTrace_8155637
  have hstable : (prefixWord ++ tailWord_8155637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155637).length < 2 ^ (prefixWord ++ tailWord_8155637).sum := by decide
  have hdescent : baseEnd_8155637 < baseStart_8155637 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8155659 : List Nat := [1, 1, 1, 1, 7, 2, 2, 1, 2, 1, 4]
def baseStart_8155659 : Nat := 118140960795 + 8155659 * 2 ^ 59
def prefixEnd_8155659 : Nat := 4983230072969 + 3 ^ 40 * 8155659 * 2
def baseEnd_8155659 : Nat := 4187773121167011680355313

theorem tailTrace_8155659 : CollatzResearch.WordTrace tailWord_8155659 prefixEnd_8155659 4187773121167011680355313 := by
  unfold tailWord_8155659
  simp only [CollatzResearch.WordTrace]
  refine ⟨297461321160447793509814031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198307547440298529006542687 297461321160447793509814031)
  ·
    refine ⟨446191981740671690264721047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297461321160447793509814031 446191981740671690264721047)
    ·
      refine ⟨669287972611007535397081571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446191981740671690264721047 669287972611007535397081571)
      ·
        refine ⟨1003931958916511303095622357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 669287972611007535397081571 1003931958916511303095622357)
        ·
          refine ⟨23529655287105733666303649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 1003931958916511303095622357 23529655287105733666303649)
          ·
            refine ⟨17647241465329300249727737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23529655287105733666303649 17647241465329300249727737)
            ·
              refine ⟨13235431098996975187295803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17647241465329300249727737 13235431098996975187295803)
              ·
                refine ⟨19853146648495462780943705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13235431098996975187295803 19853146648495462780943705)
                ·
                  refine ⟨14889859986371597085707779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19853146648495462780943705 14889859986371597085707779)
                  ·
                    refine ⟨22334789979557395628561669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14889859986371597085707779 22334789979557395628561669)
                    ·
                      refine ⟨4187773121167011680355313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22334789979557395628561669 4187773121167011680355313)
                      ·
                        rfl

theorem cell23_8155659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 2, 1, 4].length) (baseStart_8155659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155659 prefixEnd_8155659 := by exact prefixLift 8155659
  have htrace : WordTrace (prefixWord ++ tailWord_8155659) baseStart_8155659 baseEnd_8155659 := by
    simpa [prefixWord, tailWord_8155659, baseEnd_8155659] using wordTrace_append hprefix tailTrace_8155659
  have hstable : (prefixWord ++ tailWord_8155659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155659).length < 2 ^ (prefixWord ++ tailWord_8155659).sum := by decide
  have hdescent : baseEnd_8155659 < baseStart_8155659 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8155665 : List Nat := [1, 2, 2, 1, 1, 2, 2, 4, 8]
def baseStart_8155665 : Nat := 118140960795 + 8155665 * 2 ^ 59
def prefixEnd_8155665 : Nat := 4983230072969 + 3 ^ 40 * 8155665 * 2
def baseEnd_8155665 : Nat := 465308466894548739653365

theorem tailTrace_8155665 : CollatzResearch.WordTrace tailWord_8155665 prefixEnd_8155665 465308466894548739653365 := by
  unfold tailWord_8155665
  simp only [CollatzResearch.WordTrace]
  refine ⟨297461539998426056534532449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198307693332284037689688299 297461539998426056534532449)
  ·
    refine ⟨223096154998819542400899337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297461539998426056534532449 223096154998819542400899337)
    ·
      refine ⟨167322116249114656800674503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223096154998819542400899337 167322116249114656800674503)
      ·
        refine ⟨250983174373671985201011755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167322116249114656800674503 250983174373671985201011755)
        ·
          refine ⟨376474761560507977801517633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250983174373671985201011755 376474761560507977801517633)
          ·
            refine ⟨282356071170380983351138225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 376474761560507977801517633 282356071170380983351138225)
            ·
              refine ⟨211767053377785737513353669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282356071170380983351138225 211767053377785737513353669)
              ·
                refine ⟨39706322508334825783753813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 211767053377785737513353669 39706322508334825783753813)
                ·
                  refine ⟨465308466894548739653365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39706322508334825783753813 465308466894548739653365)
                  ·
                    rfl

theorem cell23_8155665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 8].length) (baseStart_8155665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155665 prefixEnd_8155665 := by exact prefixLift 8155665
  have htrace : WordTrace (prefixWord ++ tailWord_8155665) baseStart_8155665 baseEnd_8155665 := by
    simpa [prefixWord, tailWord_8155665, baseEnd_8155665] using wordTrace_append hprefix tailTrace_8155665
  have hstable : (prefixWord ++ tailWord_8155665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155665).length < 2 ^ (prefixWord ++ tailWord_8155665).sum := by decide
  have hdescent : baseEnd_8155665 < baseStart_8155665 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8155710 : List Nat := [4, 2, 1, 4, 2, 1, 1, 1, 2, 1, 4]
def baseStart_8155710 : Nat := 118140960795 + 8155710 * 2 ^ 59
def prefixEnd_8155710 : Nat := 4983230072969 + 3 ^ 40 * 8155710 * 2
def baseEnd_8155710 : Nat := 4187799308680390980817579

theorem tailTrace_8155710 : CollatzResearch.WordTrace tailWord_8155710 prefixEnd_8155710 4187799308680390980817579 := by
  unfold tailWord_8155710
  simp only [CollatzResearch.WordTrace]
  refine ⟨37182897660407878652490073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 198308787522175352813280389 37182897660407878652490073)
  ·
    refine ⟨27887173245305908989367555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37182897660407878652490073 27887173245305908989367555)
    ·
      refine ⟨41830759867958863484051333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27887173245305908989367555 41830759867958863484051333)
      ·
        refine ⟨7843267475242286903259625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41830759867958863484051333 7843267475242286903259625)
        ·
          refine ⟨5882450606431715177444719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7843267475242286903259625 5882450606431715177444719)
          ·
            refine ⟨8823675909647572766167079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5882450606431715177444719 8823675909647572766167079)
            ·
              refine ⟨13235513864471359149250619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8823675909647572766167079 13235513864471359149250619)
              ·
                refine ⟨19853270796707038723875929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13235513864471359149250619 19853270796707038723875929)
                ·
                  refine ⟨14889953097530279042906947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19853270796707038723875929 14889953097530279042906947)
                  ·
                    refine ⟨22334929646295418564360421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14889953097530279042906947 22334929646295418564360421)
                    ·
                      refine ⟨4187799308680390980817579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22334929646295418564360421 4187799308680390980817579)
                      ·
                        rfl

theorem cell23_8155710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_8155710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155710 prefixEnd_8155710 := by exact prefixLift 8155710
  have htrace : WordTrace (prefixWord ++ tailWord_8155710) baseStart_8155710 baseEnd_8155710 := by
    simpa [prefixWord, tailWord_8155710, baseEnd_8155710] using wordTrace_append hprefix tailTrace_8155710
  have hstable : (prefixWord ++ tailWord_8155710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155710).length < 2 ^ (prefixWord ++ tailWord_8155710).sum := by decide
  have hdescent : baseEnd_8155710 < baseStart_8155710 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8155712 : List Nat := [2, 1, 1, 2, 2, 2, 4, 1, 3, 5]
def baseStart_8155712 : Nat := 118140960795 + 8155712 * 2 ^ 59
def prefixEnd_8155712 : Nat := 4983230072969 + 3 ^ 40 * 8155712 * 2
def baseEnd_8155712 : Nat := 1395933445213899990997523

theorem tailTrace_8155712 : CollatzResearch.WordTrace tailWord_8155712 prefixEnd_8155712 1395933445213899990997523 := by
  unfold tailWord_8155712
  simp only [CollatzResearch.WordTrace]
  refine ⟨148731627114627891780746695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198308836152837189040995593 148731627114627891780746695)
  ·
    refine ⟨223097440671941837671120043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148731627114627891780746695 223097440671941837671120043)
    ·
      refine ⟨334646161007912756506680065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223097440671941837671120043 334646161007912756506680065)
      ·
        refine ⟨250984620755934567380010049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334646161007912756506680065 250984620755934567380010049)
        ·
          refine ⟨188238465566950925535007537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250984620755934567380010049 188238465566950925535007537)
          ·
            refine ⟨141178849175213194151255653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188238465566950925535007537 141178849175213194151255653)
            ·
              refine ⟨26471034220352473903360435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141178849175213194151255653 26471034220352473903360435)
              ·
                refine ⟨39706551330528710855040653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26471034220352473903360435 39706551330528710855040653)
                ·
                  refine ⟨14889956748948266570640245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39706551330528710855040653 14889956748948266570640245)
                  ·
                    refine ⟨1395933445213899990997523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14889956748948266570640245 1395933445213899990997523)
                    ·
                      rfl

theorem cell23_8155712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 3, 5].length) (baseStart_8155712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155712 prefixEnd_8155712 := by exact prefixLift 8155712
  have htrace : WordTrace (prefixWord ++ tailWord_8155712) baseStart_8155712 baseEnd_8155712 := by
    simpa [prefixWord, tailWord_8155712, baseEnd_8155712] using wordTrace_append hprefix tailTrace_8155712
  have hstable : (prefixWord ++ tailWord_8155712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155712).length < 2 ^ (prefixWord ++ tailWord_8155712).sum := by decide
  have hdescent : baseEnd_8155712 < baseStart_8155712 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8155729 : List Nat := [1, 2, 2, 1, 3, 4, 1, 3, 1, 5]
def baseStart_8155729 : Nat := 118140960795 + 8155729 * 2 ^ 59
def prefixEnd_8155729 : Nat := 4983230072969 + 3 ^ 40 * 8155729 * 2
def baseEnd_8155729 : Nat := 1395936354937608802159997

theorem tailTrace_8155729 : CollatzResearch.WordTrace tailWord_8155729 prefixEnd_8155729 1395936354937608802159997 := by
  unfold tailWord_8155729
  simp only [CollatzResearch.WordTrace]
  refine ⟨297463874270194195464862241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198309249513462796976574827 297463874270194195464862241)
  ·
    refine ⟨223097905702645646598646681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297463874270194195464862241 223097905702645646598646681)
    ·
      refine ⟨167323429276984234948985011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223097905702645646598646681 167323429276984234948985011)
      ·
        refine ⟨250985143915476352423477517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167323429276984234948985011 250985143915476352423477517)
        ·
          refine ⟨94119428968303632158804069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250985143915476352423477517 94119428968303632158804069)
          ·
            refine ⟨17647392931556931029775763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94119428968303632158804069 17647392931556931029775763)
            ·
              refine ⟨26471089397335396544663645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17647392931556931029775763 26471089397335396544663645)
              ·
                refine ⟨9926658524000773704248867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26471089397335396544663645 9926658524000773704248867)
                ·
                  refine ⟨14889987786001160556373301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9926658524000773704248867 14889987786001160556373301)
                  ·
                    refine ⟨1395936354937608802159997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14889987786001160556373301 1395936354937608802159997)
                    ·
                      rfl

theorem cell23_8155729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 3, 1, 5].length) (baseStart_8155729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155729 prefixEnd_8155729 := by exact prefixLift 8155729
  have htrace : WordTrace (prefixWord ++ tailWord_8155729) baseStart_8155729 baseEnd_8155729 := by
    simpa [prefixWord, tailWord_8155729, baseEnd_8155729] using wordTrace_append hprefix tailTrace_8155729
  have hstable : (prefixWord ++ tailWord_8155729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155729).length < 2 ^ (prefixWord ++ tailWord_8155729).sum := by decide
  have hdescent : baseEnd_8155729 < baseStart_8155729 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8155759 : List Nat := [1, 1, 2, 1, 3, 2, 2, 5, 2, 4]
def baseStart_8155759 : Nat := 118140960795 + 8155759 * 2 ^ 59
def prefixEnd_8155759 : Nat := 4983230072969 + 3 ^ 40 * 8155759 * 2
def baseEnd_8155759 : Nat := 1395941489744153763034951

theorem tailTrace_8155759 : CollatzResearch.WordTrace tailWord_8155759 prefixEnd_8155759 1395941489744153763034951 := by
  unfold tailWord_8155759
  simp only [CollatzResearch.WordTrace]
  refine ⟨297464968460085510588454331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198309978973390340392302887 297464968460085510588454331)
  ·
    refine ⟨446197452690128265882681497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 297464968460085510588454331 446197452690128265882681497)
    ·
      refine ⟨334648089517596199412011123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446197452690128265882681497 334648089517596199412011123)
      ·
        refine ⟨501972134276394299118016685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334648089517596199412011123 501972134276394299118016685)
        ·
          refine ⟨188239550353647862169256257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 501972134276394299118016685 188239550353647862169256257)
          ·
            refine ⟨141179662765235896626942193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188239550353647862169256257 141179662765235896626942193)
            ·
              refine ⟨105884747073926922470206645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141179662765235896626942193 105884747073926922470206645)
              ·
                refine ⟨9926695038180648981581873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105884747073926922470206645 9926695038180648981581873)
                ·
                  refine ⟨7445021278635486736186405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9926695038180648981581873 7445021278635486736186405)
                  ·
                    refine ⟨1395941489744153763034951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7445021278635486736186405 1395941489744153763034951)
                    ·
                      rfl

theorem cell23_8155759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 5, 2, 4].length) (baseStart_8155759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155759 prefixEnd_8155759 := by exact prefixLift 8155759
  have htrace : WordTrace (prefixWord ++ tailWord_8155759) baseStart_8155759 baseEnd_8155759 := by
    simpa [prefixWord, tailWord_8155759, baseEnd_8155759] using wordTrace_append hprefix tailTrace_8155759
  have hstable : (prefixWord ++ tailWord_8155759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155759).length < 2 ^ (prefixWord ++ tailWord_8155759).sum := by decide
  have hdescent : baseEnd_8155759 < baseStart_8155759 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8155786 : List Nat := [3, 1, 2, 3, 3, 1, 2, 1, 1, 1, 5]
def baseStart_8155786 : Nat := 118140960795 + 8155786 * 2 ^ 59
def prefixEnd_8155786 : Nat := 4983230072969 + 3 ^ 40 * 8155786 * 2
def baseEnd_8155786 : Nat := 4187838333210132683467229

theorem tailTrace_8155786 : CollatzResearch.WordTrace tailWord_8155786 prefixEnd_8155786 4187838333210132683467229 := by
  unfold tailWord_8155786
  simp only [CollatzResearch.WordTrace]
  refine ⟨74366488307746923549921803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198310635487325129466458141 74366488307746923549921803)
  ·
    refine ⟨111549732461620385324882705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74366488307746923549921803 111549732461620385324882705)
    ·
      refine ⟨83662299346215288993662029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111549732461620385324882705 83662299346215288993662029)
      ·
        refine ⟨31373362254830733372623261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83662299346215288993662029 31373362254830733372623261)
        ·
          refine ⟨11765010845561525014733723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31373362254830733372623261 11765010845561525014733723)
          ·
            refine ⟨17647516268342287522100585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11765010845561525014733723 17647516268342287522100585)
            ·
              refine ⟨13235637201256715641575439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17647516268342287522100585 13235637201256715641575439)
              ·
                refine ⟨19853455801885073462363159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13235637201256715641575439 19853455801885073462363159)
                ·
                  refine ⟨29780183702827610193544739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19853455801885073462363159 29780183702827610193544739)
                  ·
                    refine ⟨44670275554241415290317109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29780183702827610193544739 44670275554241415290317109)
                    ·
                      refine ⟨4187838333210132683467229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44670275554241415290317109 4187838333210132683467229)
                      ·
                        rfl

theorem cell23_8155786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_8155786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155786 prefixEnd_8155786 := by exact prefixLift 8155786
  have htrace : WordTrace (prefixWord ++ tailWord_8155786) baseStart_8155786 baseEnd_8155786 := by
    simpa [prefixWord, tailWord_8155786, baseEnd_8155786] using wordTrace_append hprefix tailTrace_8155786
  have hstable : (prefixWord ++ tailWord_8155786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155786).length < 2 ^ (prefixWord ++ tailWord_8155786).sum := by decide
  have hdescent : baseEnd_8155786 < baseStart_8155786 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8155832 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 6, 6]
def baseStart_8155832 : Nat := 118140960795 + 8155832 * 2 ^ 59
def prefixEnd_8155832 : Nat := 4983230072969 + 3 ^ 40 * 8155832 * 2
def baseEnd_8155832 : Nat := 1395953984440079834497339

theorem tailTrace_8155832 : CollatzResearch.WordTrace tailWord_8155832 prefixEnd_8155832 1395953984440079834497339 := by
  unfold tailWord_8155832
  simp only [CollatzResearch.WordTrace]
  refine ⟨148733815494410522027930875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198311753992547362703907833 148733815494410522027930875)
  ·
    refine ⟨223100723241615783041896313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148733815494410522027930875 223100723241615783041896313)
    ·
      refine ⟨167325542431211837281422235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223100723241615783041896313 167325542431211837281422235)
      ·
        refine ⟨250988313646817755922133353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167325542431211837281422235 250988313646817755922133353)
        ·
          refine ⟨188241235235113316941600015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250988313646817755922133353 188241235235113316941600015)
          ·
            refine ⟨282361852852669975412400023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188241235235113316941600015 282361852852669975412400023)
            ·
              refine ⟨423542779279004963118600035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282361852852669975412400023 423542779279004963118600035)
              ·
                refine ⟨635314168918507444677900053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 423542779279004963118600035 635314168918507444677900053)
                ·
                  refine ⟨29780351668055036469276565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 635314168918507444677900053 29780351668055036469276565)
                  ·
                    refine ⟨1395953984440079834497339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29780351668055036469276565 1395953984440079834497339)
                    ·
                      rfl

theorem cell23_8155832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 6, 6].length) (baseStart_8155832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155832 prefixEnd_8155832 := by exact prefixLift 8155832
  have htrace : WordTrace (prefixWord ++ tailWord_8155832) baseStart_8155832 baseEnd_8155832 := by
    simpa [prefixWord, tailWord_8155832, baseEnd_8155832] using wordTrace_append hprefix tailTrace_8155832
  have hstable : (prefixWord ++ tailWord_8155832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155832).length < 2 ^ (prefixWord ++ tailWord_8155832).sum := by decide
  have hdescent : baseEnd_8155832 < baseStart_8155832 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8155856 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 8, 2, 2]
def baseStart_8155856 : Nat := 118140960795 + 8155856 * 2 ^ 59
def prefixEnd_8155856 : Nat := 4983230072969 + 3 ^ 40 * 8155856 * 2
def baseEnd_8155856 : Nat := 4187874276855947409591907

theorem tailTrace_8155856 : CollatzResearch.WordTrace tailWord_8155856 prefixEnd_8155856 4187874276855947409591907 := by
  unfold tailWord_8155856
  simp only [CollatzResearch.WordTrace]
  refine ⟨148734253170367048077367711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198312337560489397436490281 148734253170367048077367711)
  ·
    refine ⟨223101379755550572116051567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148734253170367048077367711 223101379755550572116051567)
    ·
      refine ⟨334652069633325858174077351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223101379755550572116051567 334652069633325858174077351)
      ·
        refine ⟨501978104449988787261116027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334652069633325858174077351 501978104449988787261116027)
        ·
          refine ⟨752967156674983180891674041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501978104449988787261116027 752967156674983180891674041)
          ·
            refine ⟨564725367506237385668755531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 752967156674983180891674041 564725367506237385668755531)
            ·
              refine ⟨847088051259356078503133297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 564725367506237385668755531 847088051259356078503133297)
              ·
                refine ⟨635316038444517058877349973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 847088051259356078503133297 635316038444517058877349973)
                ·
                  refine ⟨7445109825521684283718945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 635316038444517058877349973 7445109825521684283718945)
                  ·
                    refine ⟨5583832369141263212789209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7445109825521684283718945 5583832369141263212789209)
                    ·
                      refine ⟨4187874276855947409591907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5583832369141263212789209 4187874276855947409591907)
                      ·
                        rfl

theorem cell23_8155856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 8, 2, 2].length) (baseStart_8155856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155856 prefixEnd_8155856 := by exact prefixLift 8155856
  have htrace : WordTrace (prefixWord ++ tailWord_8155856) baseStart_8155856 baseEnd_8155856 := by
    simpa [prefixWord, tailWord_8155856, baseEnd_8155856] using wordTrace_append hprefix tailTrace_8155856
  have hstable : (prefixWord ++ tailWord_8155856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155856).length < 2 ^ (prefixWord ++ tailWord_8155856).sum := by decide
  have hdescent : baseEnd_8155856 < baseStart_8155856 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8155873 : List Nat := [1, 2, 3, 1, 4, 2, 2, 1, 1, 4, 2]
def baseStart_8155873 : Nat := 118140960795 + 8155873 * 2 ^ 59
def prefixEnd_8155873 : Nat := 4983230072969 + 3 ^ 40 * 8155873 * 2
def baseEnd_8155873 : Nat := 4187883006027073843079329

theorem tailTrace_8155873 : CollatzResearch.WordTrace tailWord_8155873 prefixEnd_8155873 4187883006027073843079329 := by
  unfold tailWord_8155873
  simp only [CollatzResearch.WordTrace]
  refine ⟨297469126381672508058104273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198312750921115005372069515 297469126381672508058104273)
  ·
    refine ⟨223101844786254381043578205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297469126381672508058104273 223101844786254381043578205)
    ·
      refine ⟨83663191794845392891341827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223101844786254381043578205 83663191794845392891341827)
      ·
        refine ⟨125494787692268089337012741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83663191794845392891341827 125494787692268089337012741)
        ·
          refine ⟨23530272692300266750689889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125494787692268089337012741 23530272692300266750689889)
          ·
            refine ⟨17647704519225200063017417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23530272692300266750689889 17647704519225200063017417)
            ·
              refine ⟨13235778389418900047263063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17647704519225200063017417 13235778389418900047263063)
              ·
                refine ⟨19853667584128350070894595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13235778389418900047263063 19853667584128350070894595)
                ·
                  refine ⟨29780501376192525106341893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19853667584128350070894595 29780501376192525106341893)
                  ·
                    refine ⟨5583844008036098457439105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29780501376192525106341893 5583844008036098457439105)
                    ·
                      refine ⟨4187883006027073843079329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5583844008036098457439105 4187883006027073843079329)
                      ·
                        rfl

theorem cell23_8155873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 4, 2].length) (baseStart_8155873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155873 prefixEnd_8155873 := by exact prefixLift 8155873
  have htrace : WordTrace (prefixWord ++ tailWord_8155873) baseStart_8155873 baseEnd_8155873 := by
    simpa [prefixWord, tailWord_8155873, baseEnd_8155873] using wordTrace_append hprefix tailTrace_8155873
  have hstable : (prefixWord ++ tailWord_8155873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155873).length < 2 ^ (prefixWord ++ tailWord_8155873).sum := by decide
  have hdescent : baseEnd_8155873 < baseStart_8155873 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8155889 : List Nat := [1, 2, 2, 2, 2, 2, 1, 2, 1, 5, 3]
def baseStart_8155889 : Nat := 118140960795 + 8155889 * 2 ^ 59
def prefixEnd_8155889 : Nat := 4983230072969 + 3 ^ 40 * 8155889 * 2
def baseEnd_8155889 : Nat := 4187891221717545780479255

theorem tailTrace_8155889 : CollatzResearch.WordTrace tailWord_8155889 prefixEnd_8155889 4187891221717545780479255 := by
  unfold tailWord_8155889
  simp only [CollatzResearch.WordTrace]
  refine ⟨297469709949614542790686721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 198313139966409695193791147 297469709949614542790686721)
  ·
    refine ⟨223102282462210907093015041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 297469709949614542790686721 223102282462210907093015041)
    ·
      refine ⟨167326711846658180319761281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223102282462210907093015041 167326711846658180319761281)
      ·
        refine ⟨125495033884993635239820961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167326711846658180319761281 125495033884993635239820961)
        ·
          refine ⟨94121275413745226429865721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125495033884993635239820961 94121275413745226429865721)
          ·
            refine ⟨70590956560308919822399291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94121275413745226429865721 70590956560308919822399291)
            ·
              refine ⟨105886434840463379733598937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70590956560308919822399291 105886434840463379733598937)
              ·
                refine ⟨79414826130347534800199203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105886434840463379733598937 79414826130347534800199203)
                ·
                  refine ⟨119122239195521302200298805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79414826130347534800199203 119122239195521302200298805)
                  ·
                    refine ⟨11167709924580122081278013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 119122239195521302200298805 11167709924580122081278013)
                    ·
                      refine ⟨4187891221717545780479255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11167709924580122081278013 4187891221717545780479255)
                      ·
                        rfl

theorem cell23_8155889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 5, 3].length) (baseStart_8155889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155889 prefixEnd_8155889 := by exact prefixLift 8155889
  have htrace : WordTrace (prefixWord ++ tailWord_8155889) baseStart_8155889 baseEnd_8155889 := by
    simpa [prefixWord, tailWord_8155889, baseEnd_8155889] using wordTrace_append hprefix tailTrace_8155889
  have hstable : (prefixWord ++ tailWord_8155889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155889).length < 2 ^ (prefixWord ++ tailWord_8155889).sum := by decide
  have hdescent : baseEnd_8155889 < baseStart_8155889 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8155896 : List Nat := [2, 1, 2, 1, 1, 2, 6, 3, 5]
def baseStart_8155896 : Nat := 118140960795 + 8155896 * 2 ^ 59
def prefixEnd_8155896 : Nat := 4983230072969 + 3 ^ 40 * 8155896 * 2
def baseEnd_8155896 : Nat := 465321646231347472565747

theorem tailTrace_8155896 : CollatzResearch.WordTrace tailWord_8155896 prefixEnd_8155896 465321646231347472565747 := by
  unfold tailWord_8155896
  simp only [CollatzResearch.WordTrace]
  refine ⟨148734982630294591493095771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198313310173726121990794361 148734982630294591493095771)
  ·
    refine ⟨223102473945441887239643657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148734982630294591493095771 223102473945441887239643657)
    ·
      refine ⟨167326855459081415429732743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223102473945441887239643657 167326855459081415429732743)
      ·
        refine ⟨250990283188622123144599115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167326855459081415429732743 250990283188622123144599115)
        ·
          refine ⟨376485424782933184716898673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250990283188622123144599115 376485424782933184716898673)
          ·
            refine ⟨282364068587199888537674005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 376485424782933184716898673 282364068587199888537674005)
            ·
              refine ⟨13235815715024994775203469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 282364068587199888537674005 13235815715024994775203469)
              ·
                refine ⟨4963430893134373040701301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13235815715024994775203469 4963430893134373040701301)
                ·
                  refine ⟨465321646231347472565747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4963430893134373040701301 465321646231347472565747)
                  ·
                    rfl

theorem cell23_8155896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 3, 5].length) (baseStart_8155896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8155896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8155896 prefixEnd_8155896 := by exact prefixLift 8155896
  have htrace : WordTrace (prefixWord ++ tailWord_8155896) baseStart_8155896 baseEnd_8155896 := by
    simpa [prefixWord, tailWord_8155896, baseEnd_8155896] using wordTrace_append hprefix tailTrace_8155896
  have hstable : (prefixWord ++ tailWord_8155896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8155896).length < 2 ^ (prefixWord ++ tailWord_8155896).sum := by decide
  have hdescent : baseEnd_8155896 < baseStart_8155896 := by decide
  rcases family_descends (prefixWord ++ tailWord_8155896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
